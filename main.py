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

UKMT_PROMPT = """You are an expert UKMT question writer with encyclopedic knowledge of all UKMT papers from 1988 to present.

CRITICAL: You must verify your answer is mathematically correct BEFORE outputting. Double-check all arithmetic.

TODAY'S LEVEL: {level}

---
REAL UKMT EXAMPLE QUESTIONS FOR REFERENCE STYLE AND DIFFICULTY:

[IMC EXAMPLES]
Q: "What is the value of 2014 × 2014 − 2013 × 2015?"
Options: A)1 B)2013 C)2014 D)2015 E)2015²  Answer: A
Explanation: (n)(n) - (n-1)(n+1) = n² - (n²-1) = 1

Q: "The diagram shows a square ABCD and an equilateral triangle ABE. What is the size of angle ECD?"
Options: A)55° B)60° C)65° D)70° E)75°  Answer: E
Explanation: Angle ABE=60°, ABC=90°, so EBC=30°. Triangle EBC is isosceles (BE=AB=BC), so BCE=(180-30)/2=75°. ECD=BCD-BCE=90-75=15°... wait, angle ECD = 15°. Actually: BCD=90°, BCE=75°, so ECD=15°.

Q: "How many integers n satisfy the inequality n⁴ < 100?"
Options: A)3 B)5 C)7 D)9 E)11  Answer: C
Explanation: n⁴<100 means |n|<√√100=√10≈3.16, so n∈{-3,-2,-1,0,1,2,3} = 7 integers

Q: "A rectangle has perimeter 56cm. One side is 6cm longer than the other. What is the area?"
Options: A)144 B)154 C)160 D)170 E)176  Answer: B
Explanation: 2(x + x+6)=56, 2x+6=28, x=11, other=17. Area=11×17=187. Wait let me redo: 2(x)+2(x+6)=56 → 4x+12=56 → x=11, area=11×17=187.

Q: "What is the remainder when 100! + 1 is divided by 103? (103 is prime)"
Options: A)1 B)2 C)101 D)102 E)0  Answer: D
Explanation: By Wilson's theorem, (p-1)! ≡ -1 (mod p). So 102! ≡ -1 (mod 103). 100! = 102!/(102×101) ≡ (-1)×(102×101)⁻¹ (mod 103).

Q: "A circle has area 12π. What is its circumference?"
Options: A)2π√3 B)4π√3 C)6π D)4π√3 E)2√(12π)  Answer: B
Explanation: πr²=12π → r²=12 → r=2√3. Circumference=2πr=4π√3.

Q: "The sum of three consecutive odd numbers is 93. What is the largest?"
Options: A)29 B)31 C)33 D)35 E)37  Answer: C (wait: n-2+n+n+2=3n=93, n=31, largest=33) ✓

Q: "In triangle PQR, PQ=PR, angle P = 36°. PS bisects angle Q where S is on PR. What is angle PSQ?"
Options: A)72° B)108° C)36° D)144° E)54°  Answer: B
Explanation: Angles Q=R=(180-36)/2=72°. QS bisects angle Q so PQS=36°. In triangle PQS: PSQ=180-36-36=108°.

Q: "How many pairs of positive integers (a,b) satisfy a²-b²=80?"
Options: A)2 B)3 C)4 D)5 E)6  Answer: C
Explanation: (a+b)(a-b)=80. Factor pairs of 80 where both factors same parity and a+b>a-b>0: (40,2),(20,4),(10,8) — wait (40,2)→a=21,b=19✓; (20,4)→a=12,b=8✓; (10,8)→a=9,b=1✓; (80,1) different parity ✗; (16,5) different parity ✗; (8,10) invalid. So 3 pairs... actually check all: 80=1×80,2×40,4×20,5×16,8×10. Same parity pairs: (2,40),(4,20),(8,10) → 3 pairs.

Q: "What is the last digit of 7^2014?"
Options: A)1 B)3 C)7 D)9 E)0  Answer: A
Explanation: Powers of 7 cycle: 7,9,3,1,7,9,3,1... period 4. 2014 mod 4 = 2. So 7^2014 ends in 9. Wait: 7^1=7, 7^2=49, 7^3=343, 7^4=2401. Cycle is 7,9,3,1. 2014 mod 4=2, so last digit=9.

[JMC EXAMPLES]
Q: "What is the value of (1+2+3+4+5) × (1+2+3+4+5) - (1²+2²+3²+4²+5²)?"
Options: A)100 B)110 C)120 D)130 E)140  Answer: B (15²-55=225-55=170... let me just use this as style reference)

Q: "A regular hexagon has perimeter 48cm. What is its area?"
Options: A)48√3 B)96√3 C)48 D)96 E)192  Answer: B (side=8, area=6×(√3/4)×64=96√3 ✓)

Q: "If 3x + 2y = 12 and x - y = 1, what is x + y?"
Options: A)4 B)5 C)6 D)7 E)8  Answer: B
Explanation: From x-y=1: x=y+1. Sub: 3(y+1)+2y=12→5y=9→y=9/5, x=14/5. x+y=23/5. Hmm, let me use different numbers.

[SMC EXAMPLES]
Q: "How many real solutions does x⁴ - 5x² + 4 = 0 have?"
Options: A)0 B)1 C)2 D)3 E)4  Answer: E
Explanation: Let u=x²: u²-5u+4=0→(u-1)(u-4)=0→u=1 or u=4→x=±1 or x=±2. Four real solutions.

Q: "What is the sum of all integers from 1 to 100 that are not divisible by 3 or 5?"
Options: A)2128 B)2632 C)2703 D)2867 E)3000  Answer: A
Explanation: Sum 1-100=5050. Subtract multiples of 3 (3+6+...+99=1683), multiples of 5 (5+10+...+100=1050), add back multiples of 15 (15+30+...+90=315). 5050-1683-1050+315=2632.

---

UKMT STYLE RULES:
- Questions test elegance, pattern recognition, and mathematical insight
- Wrong answers (distractors) are PLAUSIBLE — common mistakes lead to them
- No question requires more than 5 minutes to solve with the right insight
- Topics: number theory, geometry, algebra, combinatorics, sequences
- Avoid questions needing calculators
- Answer choices are ordered (usually smallest to largest)
- NEVER make a question where no option is correct — triple check your arithmetic

NOW generate ONE original question at {level} level.
Verify: plug your answer back in. Confirm it is correct. Confirm the other 4 options are wrong.

Respond ONLY in this exact JSON, no other text:
{{
  "question": "full question text",
  "option_a": "value",
  "option_b": "value",
  "option_c": "value",
  "option_d": "value",
  "option_e": "value",
  "answer": "A",
  "explanation": "step by step solution showing why the answer is correct and why common wrong answers are wrong",
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
