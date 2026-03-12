import os
import json
import sqlite3
import time
import requests
from datetime import datetime, date
from flask import Flask, render_template, request, jsonify
from groq import Groq
from apscheduler.schedulers.background import BackgroundScheduler

app = Flask(__name__)

GROQ_API_KEY = os.environ.get('GROQ_API_KEY')
DISCORD_WEBHOOK = os.environ.get('DISCORD_WEBHOOK')

client = Groq(api_key=GROQ_API_KEY)

def get_db():
    conn = sqlite3.connect('questions.db')
    conn.row_factory = sqlite3.Row
    return conn

def init_db():
    conn = get_db()
    conn.execute('''CREATE TABLE IF NOT EXISTS questions (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        date TEXT UNIQUE,
        question TEXT,
        option_a TEXT,
        option_b TEXT,
        option_c TEXT,
        option_d TEXT,
        option_e TEXT,
        answer TEXT,
        explanation TEXT,
        level TEXT
    )''')
    conn.execute('''CREATE TABLE IF NOT EXISTS submissions (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        date TEXT,
        mc_username TEXT,
        discord_username TEXT,
        answer TEXT,
        is_correct INTEGER,
        submitted_at INTEGER
    )''')
    conn.commit()
    conn.close()

init_db()

UKMT_PROMPT = """You are an expert UKMT question writer with deep knowledge of all past UKMT papers including Junior, Intermediate, and Senior Mathematical Challenges from 1988 to present.

Generate a single UKMT-style multiple choice question. Today's level: {level}.

STRICT requirements:
- Must be genuinely UKMT style — elegant, tricky, requires insight not just calculation
- 5 options labeled A, B, C, D, E
- One correct answer
- Appropriate difficulty for {level} level
- Include a clear explanation of the solution

Respond ONLY in this exact JSON format, nothing else:
{{
  "question": "full question text here",
  "option_a": "value",
  "option_b": "value", 
  "option_c": "value",
  "option_d": "value",
  "option_e": "value",
  "answer": "A",
  "explanation": "full solution explanation here",
  "level": "{level}"
}}"""

def pick_level():
    import random
    # 70% Intermediate, 30% mixed
    if random.random() < 0.7:
        return "Intermediate (IMC)"
    return random.choice(["Junior (JMC)", "Intermediate (IMC)", "Senior (SMC)"])

def generate_question():
    today = date.today().isoformat()
    conn = get_db()
    existing = conn.execute('SELECT id FROM questions WHERE date = ?', (today,)).fetchone()
    conn.close()
    if existing:
        return

    level = pick_level()
    try:
        response = client.chat.completions.create(
            model="llama-3.3-70b-versatile",
            messages=[{"role": "user", "content": UKMT_PROMPT.format(level=level)}],
            temperature=0.8,
            max_tokens=1000
        )
        raw = response.choices[0].message.content.strip()
        data = json.loads(raw)

        conn = get_db()
        conn.execute('''INSERT OR IGNORE INTO questions 
            (date, question, option_a, option_b, option_c, option_d, option_e, answer, explanation, level)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)''',
            (today, data['question'], data['option_a'], data['option_b'],
             data['option_c'], data['option_d'], data['option_e'],
             data['answer'], data['explanation'], data['level']))
        conn.commit()
        conn.close()
        print(f"✅ Question generated for {today}")
    except Exception as e:
        print(f"❌ Failed to generate question: {e}")

def send_discord_submission(mc_username, discord_username, answer, is_correct, question_text, date_str):
    if not DISCORD_WEBHOOK:
        return
    color = 0x6BCF7F if is_correct else 0xFF6B6B
    payload = {
        "embeds": [{
            "title": "📐 New UKMT Submission!",
            "color": color,
            "fields": [
                {"name": "Minecraft Username", "value": mc_username, "inline": True},
                {"name": "Discord Username", "value": discord_username, "inline": True},
                {"name": "Answer Submitted", "value": answer, "inline": True},
                {"name": "Result", "value": "✅ Correct!" if is_correct else "❌ Wrong", "inline": True},
                {"name": "Question Date", "value": date_str, "inline": True},
                {"name": "Question", "value": question_text[:200] + "..." if len(question_text) > 200 else question_text, "inline": False}
            ],
            "timestamp": datetime.utcnow().isoformat()
        }]
    }
    try:
        requests.post(DISCORD_WEBHOOK, json=payload, timeout=5)
    except:
        pass

# Schedule daily question at midnight UTC
scheduler = BackgroundScheduler()
scheduler.add_job(generate_question, 'cron', hour=0, minute=0)
scheduler.start()

@app.route('/')
def home():
    generate_question()  # ensure today's question exists
    return render_template('index.html')

@app.route('/sw.js')
def service_worker():
    from flask import send_from_directory
    return send_from_directory('static', 'sw.js', mimetype='application/javascript')

@app.route('/question')
def get_question():
    today = date.today().isoformat()
    conn = get_db()
    q = conn.execute('SELECT * FROM questions WHERE date = ?', (today,)).fetchone()

    # Get yesterday's question for answer reveal
    from datetime import timedelta
    yesterday = (date.today() - timedelta(days=1)).isoformat()
    yq = conn.execute('SELECT * FROM questions WHERE date = ?', (yesterday,)).fetchone()
    conn.close()

    if not q:
        return jsonify({'error': 'No question yet'}), 404

    return jsonify({
        'today': {
            'date': q['date'],
            'question': q['question'],
            'option_a': q['option_a'],
            'option_b': q['option_b'],
            'option_c': q['option_c'],
            'option_d': q['option_d'],
            'option_e': q['option_e'],
            'level': q['level']
        },
        'yesterday': {
            'date': yq['date'],
            'question': yq['question'],
            'answer': yq['answer'],
            'explanation': yq['explanation'],
            'level': yq['level']
        } if yq else None
    })

@app.route('/submit', methods=['POST'])
def submit():
    data = request.get_json()
    mc_username = data.get('mc_username', '').strip()
    discord_username = data.get('discord_username', '').strip()
    answer = data.get('answer', '').strip().upper()
    today = date.today().isoformat()

    if not mc_username or not discord_username or not answer:
        return jsonify({'success': False, 'error': 'Missing fields'})

    if len(mc_username) > 16 or len(discord_username) > 32:
        return jsonify({'success': False, 'error': 'Invalid username length'})

    if answer not in ['A', 'B', 'C', 'D', 'E']:
        return jsonify({'success': False, 'error': 'Invalid answer'})

    conn = get_db()

    # Check already submitted today
    existing = conn.execute(
        'SELECT id FROM submissions WHERE date = ? AND mc_username = ?',
        (today, mc_username)
    ).fetchone()
    if existing:
        conn.close()
        return jsonify({'success': False, 'error': 'Already submitted today!'})

    q = conn.execute('SELECT * FROM questions WHERE date = ?', (today,)).fetchone()
    if not q:
        conn.close()
        return jsonify({'success': False, 'error': 'No question found'})

    is_correct = answer == q['answer']

    conn.execute('''INSERT INTO submissions (date, mc_username, discord_username, answer, is_correct, submitted_at)
                    VALUES (?, ?, ?, ?, ?, ?)''',
                 (today, mc_username, discord_username, answer, int(is_correct), int(time.time())))
    conn.commit()
    conn.close()

    send_discord_submission(mc_username, discord_username, answer, is_correct, q['question'], today)

    return jsonify({'success': True, 'submitted': True})

@app.route('/leaderboard')
def leaderboard():
    conn = get_db()
    users = conn.execute('''
        SELECT mc_username, 
               COUNT(*) as total,
               SUM(is_correct) as correct
        FROM submissions
        GROUP BY mc_username
        ORDER BY correct DESC
        LIMIT 20
    ''').fetchall()
    conn.close()
    return jsonify([dict(u) for u in users])

if __name__ == '__main__':
    app.run()
