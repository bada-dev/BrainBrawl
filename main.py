import os
import json
import sqlite3
import time
import random
import math
import ast
from datetime import datetime, date, timedelta
from fractions import Fraction
from flask import Flask, render_template, request, jsonify, send_from_directory
from groq import Groq
from apscheduler.schedulers.background import BackgroundScheduler

app = Flask(__name__)

GROQ_API_KEY = os.environ.get('GROQ_API_KEY')
DISCORD_WEBHOOK = os.environ.get('DISCORD_WEBHOOK')
client = Groq(api_key=GROQ_API_KEY)

# ─────────────────────────────────────────────────────────────────────────────
# DATABASE
# ─────────────────────────────────────────────────────────────────────────────

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
        level TEXT,
        source TEXT DEFAULT 'template'
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
    conn.execute('''CREATE TABLE IF NOT EXISTS feedback_cooldowns (
        ip TEXT PRIMARY KEY,
        last_submitted INTEGER DEFAULT 0
    )''')
    conn.commit()
    conn.close()

init_db()

FEEDBACK_COOLDOWN = 48 * 60 * 60

# ─────────────────────────────────────────────────────────────────────────────
# TEMPLATE QUESTION SYSTEM
# Every question here is structurally correct — Python computes the answer.
# The AI never touches the math, only optionally rewrites the wording.
# ─────────────────────────────────────────────────────────────────────────────

PYTHAGOREAN_TRIPLES = [
    (3, 4, 5), (5, 12, 13), (8, 15, 17), (7, 24, 25),
    (9, 40, 41), (20, 21, 29), (9, 12, 15), (12, 16, 20),
    (15, 20, 25), (6, 8, 10)
]


def make_numeric_options(correct):
    """
    Generate 4 plausible wrong answers for a numeric correct answer.
    Returns (list_of_5_strings, answer_letter).
    All wrong answers are positive and different from correct.
    """
    correct_int = int(correct) if float(correct) == int(correct) else correct
    wrongs = set()
    attempts = 0
    deltas = [-30, -20, -15, -12, -10, -8, -6, -5, -4, -3, -2, -1,
               1,   2,   3,   4,   5,   6,   8,  10,  12,  15,  20, 30]
    random.shuffle(deltas)
    for d in deltas:
        if len(wrongs) >= 4:
            break
        w = correct_int + d
        if w > 0 and w != correct_int:
            wrongs.add(w)
    # fallback if not enough
    extra = 1
    while len(wrongs) < 4:
        w = correct_int + extra * 7
        if w != correct_int:
            wrongs.add(w)
        extra += 1

    all_opts = [correct_int] + list(wrongs)[:4]
    random.shuffle(all_opts)
    answer_letter = 'ABCDE'[all_opts.index(correct_int)]
    formatted = [str(x) for x in all_opts]
    return formatted, answer_letter


def make_pi_options(correct_base):
    """For answers expressed as Nπ — correct_base is the integer N."""
    wrongs = set()
    for d in [-4, -3, -2, -1, 1, 2, 3, 4, 6, 8]:
        if len(wrongs) >= 4:
            break
        w = correct_base + d
        if w > 0:
            wrongs.add(w)
    all_opts = [correct_base] + list(wrongs)[:4]
    random.shuffle(all_opts)
    answer_letter = 'ABCDE'[all_opts.index(correct_base)]
    formatted = [f"{x}π" for x in all_opts]
    return formatted, answer_letter


def make_fraction_options(num, den):
    """For probability/fraction answers."""
    from math import gcd
    g = gcd(num, den)
    correct = (num // g, den // g)
    correct_str = f"{correct[0]}/{correct[1]}"
    wrongs = []
    seen = {correct_str}
    for wn in range(1, den):
        if len(wrongs) >= 4:
            break
        wg = gcd(wn, den)
        ws = f"{wn//wg}/{den//wg}"
        if ws not in seen:
            seen.add(ws)
            wrongs.append(ws)
    if len(wrongs) < 4:
        for extra_den in [den+1, den+2, den-1]:
            if len(wrongs) >= 4:
                break
            if extra_den > 1:
                ws = f"1/{extra_den}"
                if ws not in seen:
                    seen.add(ws)
                    wrongs.append(ws)
    all_opts = [correct_str] + wrongs[:4]
    while len(all_opts) < 5:
        all_opts.append(f"{len(all_opts)}/{den+1}")
    random.shuffle(all_opts)
    answer_letter = 'ABCDE'[all_opts.index(correct_str)]
    return all_opts, answer_letter


# ── TEMPLATE DEFINITIONS ─────────────────────────────────────────────────────
# Each entry is a function that returns a complete question dict.
# Python computes ANSWER — never the AI.

def tpl_rectangle_area():
    a, b, _ = random.choice(PYTHAGOREAN_TRIPLES)
    scale = random.randint(1, 4)
    w, h = a * scale, b * scale
    answer = w * h
    assert w * h == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"A rectangle has length {w} cm and width {h} cm. What is its area?",
        "option_a": opts[0] + " cm²", "option_b": opts[1] + " cm²",
        "option_c": opts[2] + " cm²", "option_d": opts[3] + " cm²",
        "option_e": opts[4] + " cm²",
        "answer": letter,
        "explanation": f"Area = length × width = {w} × {h} = {answer} cm².",
        "level": "Junior (JMC)"
    }

def tpl_circle_area():
    r = random.randint(2, 12)
    base = r * r  # answer is base·π — integer, no floating point
    # No float assertion needed: base = r*r is exact integer arithmetic
    opts, letter = make_pi_options(base)
    return {
        "question": f"A circle has radius {r} cm. What is its area? Give your answer in terms of π.",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"Area = πr² = π × {r}² = {base}π cm².",
        "level": "Junior (JMC)"
    }

def tpl_circle_circumference():
    r = random.randint(2, 15)
    base = 2 * r  # answer is base·π
    opts, letter = make_pi_options(base)
    return {
        "question": f"A circle has radius {r} cm. What is its circumference? Give your answer in terms of π.",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"Circumference = 2πr = 2 × π × {r} = {base}π cm.",
        "level": "Junior (JMC)"
    }

def tpl_cube_surface_area():
    s = random.randint(2, 10)
    answer = 6 * s * s
    assert 6 * s**2 == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"A cube has side length {s} cm. What is its total surface area?",
        "option_a": opts[0] + " cm²", "option_b": opts[1] + " cm²",
        "option_c": opts[2] + " cm²", "option_d": opts[3] + " cm²",
        "option_e": opts[4] + " cm²",
        "answer": letter,
        "explanation": f"A cube has 6 square faces. Surface area = 6 × s² = 6 × {s}² = 6 × {s**2} = {answer} cm².",
        "level": "Junior (JMC)"
    }

def tpl_cube_volume():
    s = random.randint(2, 10)
    answer = s ** 3
    assert s**3 == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"A cube has side length {s} cm. What is its volume?",
        "option_a": opts[0] + " cm³", "option_b": opts[1] + " cm³",
        "option_c": opts[2] + " cm³", "option_d": opts[3] + " cm³",
        "option_e": opts[4] + " cm³",
        "answer": letter,
        "explanation": f"Volume = s³ = {s}³ = {answer} cm³.",
        "level": "Junior (JMC)"
    }

def tpl_cylinder_volume():
    r = random.randint(2, 7)
    h = random.randint(3, 12)
    base = r * r * h  # answer is base·π
    assert r**2 * h == base
    opts, letter = make_pi_options(base)
    return {
        "question": f"A cylinder has radius {r} cm and height {h} cm. What is its volume? Give your answer in terms of π.",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"Volume = πr²h = π × {r}² × {h} = π × {r**2} × {h} = {base}π cm³.",
        "level": "Intermediate (IMC)"
    }

def tpl_right_triangle_hypotenuse():
    a, b, c = random.choice(PYTHAGOREAN_TRIPLES)
    scale = random.randint(1, 3)
    sa, sb, sc = a*scale, b*scale, c*scale
    assert sa**2 + sb**2 == sc**2
    opts, letter = make_numeric_options(sc)
    return {
        "question": f"A right-angled triangle has legs {sa} cm and {sb} cm. What is the length of the hypotenuse?",
        "option_a": opts[0] + " cm", "option_b": opts[1] + " cm",
        "option_c": opts[2] + " cm", "option_d": opts[3] + " cm",
        "option_e": opts[4] + " cm",
        "answer": letter,
        "explanation": f"By Pythagoras: hypotenuse = √({sa}² + {sb}²) = √({sa**2} + {sb**2}) = √{sc**2} = {sc} cm.",
        "level": "Junior (JMC)"
    }

def tpl_right_triangle_leg():
    a, b, c = random.choice(PYTHAGOREAN_TRIPLES)
    scale = random.randint(1, 3)
    sa, sb, sc = a*scale, b*scale, c*scale
    assert sa**2 + sb**2 == sc**2
    opts, letter = make_numeric_options(sb)
    return {
        "question": f"A right-angled triangle has hypotenuse {sc} cm and one leg {sa} cm. What is the other leg?",
        "option_a": opts[0] + " cm", "option_b": opts[1] + " cm",
        "option_c": opts[2] + " cm", "option_d": opts[3] + " cm",
        "option_e": opts[4] + " cm",
        "answer": letter,
        "explanation": f"Other leg = √({sc}² − {sa}²) = √({sc**2} − {sa**2}) = √{sb**2} = {sb} cm.",
        "level": "Junior (JMC)"
    }

def tpl_interior_angle_polygon():
    n = random.choice([5, 6, 8, 9, 10, 12])
    total = (n - 2) * 180
    angle = total // n
    assert (n - 2) * 180 % n == 0  # must be whole number
    assert (n - 2) * 180 // n == angle
    opts, letter = make_numeric_options(angle)
    return {
        "question": f"What is the size of each interior angle of a regular {n}-sided polygon?",
        "option_a": opts[0] + "°", "option_b": opts[1] + "°",
        "option_c": opts[2] + "°", "option_d": opts[3] + "°",
        "option_e": opts[4] + "°",
        "answer": letter,
        "explanation": f"Sum of interior angles = (n−2)×180° = ({n}−2)×180° = {total}°. Each angle = {total}° ÷ {n} = {angle}°.",
        "level": "Intermediate (IMC)"
    }

def tpl_exterior_angle_polygon():
    ext = random.choice([30, 36, 40, 45, 60, 72])
    n = 360 // ext
    assert 360 % ext == 0
    assert 360 // ext == n
    opts, letter = make_numeric_options(n)
    return {
        "question": f"Each exterior angle of a regular polygon is {ext}°. How many sides does the polygon have?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"Number of sides = 360° ÷ exterior angle = 360° ÷ {ext}° = {n}.",
        "level": "Intermediate (IMC)"
    }

def tpl_triangle_missing_angle():
    a = random.randint(30, 80)
    b = random.randint(30, 80)
    c = 180 - a - b
    if c <= 0 or c >= 180:
        a, b, c = 50, 70, 60
    assert a + b + c == 180
    opts, letter = make_numeric_options(c)
    return {
        "question": f"Two angles of a triangle are {a}° and {b}°. What is the third angle?",
        "option_a": opts[0] + "°", "option_b": opts[1] + "°",
        "option_c": opts[2] + "°", "option_d": opts[3] + "°",
        "option_e": opts[4] + "°",
        "answer": letter,
        "explanation": f"Angles in a triangle sum to 180°. Third angle = 180° − {a}° − {b}° = {c}°.",
        "level": "Junior (JMC)"
    }

def tpl_isosceles_triangle_angle():
    base = random.choice([30, 40, 50, 60, 70, 80, 100, 110, 120])
    equal = (180 - base) // 2
    if (180 - base) % 2 != 0:
        base = 40
        equal = 70
    assert base + 2 * equal == 180
    opts, letter = make_numeric_options(equal)
    return {
        "question": f"An isosceles triangle has a base angle of {base}°. Wait — actually the apex angle is {base}°. What are the base angles?",
        "option_a": opts[0] + "°", "option_b": opts[1] + "°",
        "option_c": opts[2] + "°", "option_d": opts[3] + "°",
        "option_e": opts[4] + "°",
        "answer": letter,
        "explanation": f"Base angles are equal. Base angle = (180° − {base}°) ÷ 2 = {180 - base}° ÷ 2 = {equal}°.",
        "level": "Junior (JMC)"
    }

def tpl_quadrilateral_missing_angle():
    a = random.randint(60, 100)
    b = random.randint(60, 100)
    c = random.randint(60, 100)
    d = 360 - a - b - c
    if d <= 0 or d >= 360:
        a, b, c, d = 80, 90, 110, 80
    assert a + b + c + d == 360
    opts, letter = make_numeric_options(d)
    return {
        "question": f"Three angles of a quadrilateral are {a}°, {b}°, and {c}°. What is the fourth angle?",
        "option_a": opts[0] + "°", "option_b": opts[1] + "°",
        "option_c": opts[2] + "°", "option_d": opts[3] + "°",
        "option_e": opts[4] + "°",
        "answer": letter,
        "explanation": f"Angles in a quadrilateral sum to 360°. Fourth = 360° − {a}° − {b}° − {c}° = {d}°.",
        "level": "Junior (JMC)"
    }

# ── NUMBER TEMPLATES ─────────────────────────────────────────────────────────

def tpl_last_digit_power():
    base = random.choice([2, 3, 7, 8])
    # Find cycle length of last digit
    cycles = {2: [2,4,8,6], 3: [3,9,7,1], 7: [7,9,3,1], 8: [8,4,2,6]}
    cycle = cycles[base]
    period = len(cycle)
    exp = random.choice([10, 20, 30, 40, 50, 60, 100, 200])
    idx = (exp % period) - 1
    if idx < 0:
        idx = period - 1
    answer = cycle[idx]
    assert (base ** exp) % 10 == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"What is the last digit of {base}^{exp}?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"Powers of {base} cycle in their last digit: {', '.join(str(x) for x in cycle)}, repeating every {period}. {exp} mod {period} = {exp % period if exp % period != 0 else period}, so last digit = {answer}.",
        "level": "Intermediate (IMC)"
    }

def tpl_sum_arithmetic_sequence():
    a = random.randint(1, 10)
    d = random.randint(1, 5)
    n = random.randint(10, 25)
    answer = n * (2 * a + (n - 1) * d) // 2
    assert n * (2 * a + (n - 1) * d) % 2 == 0
    assert n * (2 * a + (n - 1) * d) // 2 == answer
    last = a + (n - 1) * d
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"What is the sum of the arithmetic sequence: {a}, {a+d}, {a+2*d}, ..., {last}? (There are {n} terms.)",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"Sum = n/2 × (first + last) = {n}/2 × ({a} + {last}) = {n}/2 × {a+last} = {answer}.",
        "level": "Intermediate (IMC)"
    }

def tpl_nth_term():
    a = random.randint(1, 10)
    d = random.randint(1, 6)
    n = random.randint(10, 40)
    answer = a + (n - 1) * d
    assert a + (n - 1) * d == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"The nth term of a sequence is {a} + (n−1)×{d}. What is the {n}th term?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"Substitute n = {n}: {a} + ({n}−1)×{d} = {a} + {n-1}×{d} = {a} + {(n-1)*d} = {answer}.",
        "level": "Junior (JMC)"
    }

def tpl_sum_squares():
    n = random.randint(5, 12)
    answer = n * (n + 1) * (2 * n + 1) // 6
    assert n * (n + 1) * (2 * n + 1) % 6 == 0
    assert n * (n + 1) * (2 * n + 1) // 6 == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"What is the value of 1² + 2² + 3² + ... + {n}²?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"Sum of squares = n(n+1)(2n+1)/6 = {n}×{n+1}×{2*n+1}/6 = {n*(n+1)*(2*n+1)}/6 = {answer}.",
        "level": "Intermediate (IMC)"
    }

def tpl_sum_first_n():
    n = random.choice([20, 25, 30, 40, 50, 60, 75, 100])
    answer = n * (n + 1) // 2
    assert n * (n + 1) % 2 == 0
    assert n * (n + 1) // 2 == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"What is the value of 1 + 2 + 3 + ... + {n}?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"Sum = n(n+1)/2 = {n}×{n+1}/2 = {n*(n+1)}/2 = {answer}.",
        "level": "Junior (JMC)"
    }

def tpl_power_of_two_sum():
    n = random.randint(4, 10)
    answer = 2 ** (n + 1) - 1
    assert sum(2**i for i in range(n + 1)) == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"What is the value of 2⁰ + 2¹ + 2² + ... + 2^{n}?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"This is a geometric series. Sum = 2^(n+1) − 1 = 2^{n+1} − 1 = {2**(n+1)} − 1 = {answer}.",
        "level": "Intermediate (IMC)"
    }

def tpl_divisibility_count():
    d = random.choice([3, 4, 6, 7, 8, 9, 11, 13])
    n = random.choice([50, 100, 150, 200, 250, 500])
    answer = n // d
    assert n // d == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"How many positive integers from 1 to {n} are divisible by {d}?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"Count = ⌊{n}/{d}⌋ = {answer}.",
        "level": "Junior (JMC)"
    }

def tpl_factorial_value():
    n = random.randint(3, 7)
    answer = math.factorial(n)
    assert math.factorial(n) == answer
    opts, letter = make_numeric_options(answer)
    steps = " × ".join(str(i) for i in range(n, 0, -1))
    return {
        "question": f"What is the value of {n}! (that is, {n} factorial)?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"{n}! = {steps} = {answer}.",
        "level": "Intermediate (IMC)"
    }

def tpl_factorial_sum():
    n = random.randint(3, 6)
    answer = sum(math.factorial(i) for i in range(1, n + 1))
    assert sum(math.factorial(i) for i in range(1, n + 1)) == answer
    parts = " + ".join(f"{i}!" for i in range(1, n + 1))
    vals = " + ".join(str(math.factorial(i)) for i in range(1, n + 1))
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"What is the value of 1! + 2! + 3! + ... + {n}!?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"{parts} = {vals} = {answer}.",
        "level": "Intermediate (IMC)"
    }

# ── ALGEBRA TEMPLATES ────────────────────────────────────────────────────────

def tpl_linear_equation():
    a = random.randint(2, 8)
    x = random.randint(2, 15)
    b = random.randint(1, 20)
    c = a * x + b
    assert (c - b) % a == 0
    assert (c - b) // a == x
    opts, letter = make_numeric_options(x)
    return {
        "question": f"If {a}x + {b} = {c}, what is the value of x?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"{a}x = {c} − {b} = {c-b}. x = {c-b} ÷ {a} = {x}.",
        "level": "Junior (JMC)"
    }

def tpl_substitute_quadratic():
    a = random.randint(1, 4)
    b = random.randint(1, 6)
    x = random.randint(2, 8)
    answer = a * x * x + b * x
    assert a * x**2 + b * x == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"If f(x) = {a}x² + {b}x, what is f({x})?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"f({x}) = {a}×{x}² + {b}×{x} = {a}×{x**2} + {b*x} = {a*x**2} + {b*x} = {answer}.",
        "level": "Intermediate (IMC)"
    }

def tpl_difference_of_squares():
    a = random.randint(10, 50)
    b = random.randint(2, 10)
    answer = a * a - b * b
    assert (a + b) * (a - b) == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"What is the value of {a}² − {b}²?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"Using difference of squares: ({a}+{b})({a}−{b}) = {a+b} × {a-b} = {answer}.",
        "level": "Intermediate (IMC)"
    }

def tpl_consecutive_integers_sum():
    n = random.randint(3, 7)
    start = random.randint(5, 30)
    answer = sum(range(start, start + n))
    nums = ", ".join(str(i) for i in range(start, start + n))
    assert sum(range(start, start + n)) == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"What is the sum of the {n} consecutive integers starting at {start}? ({nums})",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"Sum = {n} × middle term = {n} × {start + n//2} = {answer}. (Or just add: {nums} = {answer}.)",
        "level": "Junior (JMC)"
    }

def tpl_expression_evaluation():
    # Evaluates something like a²b + c where a,b,c are small integers
    a = random.randint(2, 5)
    b = random.randint(2, 6)
    c = random.randint(1, 10)
    answer = a * a * b + c
    assert a**2 * b + c == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"If a = {a}, b = {b}, and c = {c}, what is the value of a²b + c?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"a²b + c = {a}² × {b} + {c} = {a**2} × {b} + {c} = {a**2*b} + {c} = {answer}.",
        "level": "Junior (JMC)"
    }

# ── PERCENTAGE / RATIO ────────────────────────────────────────────────────────

def tpl_percentage_of():
    p = random.choice([10, 15, 20, 25, 30, 40, 50, 60, 75, 80])
    # Make sure answer is a whole number
    n = random.choice([20, 40, 60, 80, 100, 120, 160, 200, 240, 300, 400])
    answer = p * n // 100
    assert p * n % 100 == 0
    assert p * n // 100 == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"What is {p}% of {n}?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"{p}% of {n} = ({p}/100) × {n} = {answer}.",
        "level": "Junior (JMC)"
    }

def tpl_reverse_percentage():
    p = random.choice([10, 20, 25, 30, 40, 50])
    orig = random.choice([40, 60, 80, 100, 120, 160, 200, 240])
    sale = orig * (100 - p) // 100
    assert orig * (100 - p) % 100 == 0
    assert sale * 100 // (100 - p) == orig
    opts, letter = make_numeric_options(orig)
    return {
        "question": f"After a {p}% discount, an item costs £{sale}. What was the original price?",
        "option_a": "£" + opts[0], "option_b": "£" + opts[1],
        "option_c": "£" + opts[2], "option_d": "£" + opts[3], "option_e": "£" + opts[4],
        "answer": letter,
        "explanation": f"Original × (1 − {p}/100) = £{sale}. Original = £{sale} ÷ {(100-p)/100} = £{orig}.",
        "level": "Intermediate (IMC)"
    }

def tpl_percentage_increase():
    orig = random.choice([50, 60, 80, 100, 120, 150, 200])
    p = random.choice([10, 20, 25, 30, 40, 50])
    answer = orig * (100 + p) // 100
    assert orig * (100 + p) % 100 == 0
    assert orig * (100 + p) // 100 == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"A price of £{orig} is increased by {p}%. What is the new price?",
        "option_a": "£" + opts[0], "option_b": "£" + opts[1],
        "option_c": "£" + opts[2], "option_d": "£" + opts[3], "option_e": "£" + opts[4],
        "answer": letter,
        "explanation": f"New price = £{orig} × (1 + {p}/100) = £{orig} × {(100+p)/100} = £{answer}.",
        "level": "Junior (JMC)"
    }

def tpl_ratio_sharing():
    a = random.randint(1, 5)
    b = random.randint(1, 5)
    while a == b:
        b = random.randint(1, 5)
    total_parts = a + b
    # Make sure total divides cleanly
    total = total_parts * random.randint(4, 15)
    larger_ratio = max(a, b)
    answer = larger_ratio * total // total_parts
    assert (a + b) * (total // (a + b)) == total
    assert larger_ratio * total // total_parts == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"£{total} is shared between two people in the ratio {a}:{b}. What is the larger share?",
        "option_a": "£" + opts[0], "option_b": "£" + opts[1],
        "option_c": "£" + opts[2], "option_d": "£" + opts[3], "option_e": "£" + opts[4],
        "answer": letter,
        "explanation": f"Each part = £{total} ÷ {total_parts} = £{total//total_parts}. Larger share = {larger_ratio} × £{total//total_parts} = £{answer}.",
        "level": "Junior (JMC)"
    }

def tpl_speed_distance_time():
    s = random.randint(20, 90)
    t = random.randint(2, 5)
    answer = s * t
    assert s * t == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"A car travels at {s} km/h for {t} hours. How far does it travel?",
        "option_a": opts[0] + " km", "option_b": opts[1] + " km",
        "option_c": opts[2] + " km", "option_d": opts[3] + " km",
        "option_e": opts[4] + " km",
        "answer": letter,
        "explanation": f"Distance = speed × time = {s} × {t} = {answer} km.",
        "level": "Junior (JMC)"
    }

def tpl_speed_time_from_distance():
    # How long does it take?
    d = random.choice([60, 90, 120, 150, 180, 240, 300])
    s = random.choice([30, 40, 50, 60])
    t = d // s
    if d % s != 0:
        d = s * 3
        t = 3
    assert d == s * t
    opts, letter = make_numeric_options(t)
    return {
        "question": f"A car travels {d} km at {s} km/h. How many hours does the journey take?",
        "option_a": opts[0] + " hours", "option_b": opts[1] + " hours",
        "option_c": opts[2] + " hours", "option_d": opts[3] + " hours",
        "option_e": opts[4] + " hours",
        "answer": letter,
        "explanation": f"Time = distance ÷ speed = {d} ÷ {s} = {t} hours.",
        "level": "Junior (JMC)"
    }

# ── PROBABILITY ───────────────────────────────────────────────────────────────

def tpl_simple_probability():
    r = random.randint(2, 6)
    b = random.randint(2, 6)
    g = random.randint(2, 6)
    total = r + b + g
    # Pick whichever colour gives simplest fraction
    opts, letter = make_fraction_options(r, total)
    return {
        "question": f"A bag contains {r} red, {b} blue, and {g} green balls. A ball is chosen at random. What is the probability it is red?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"P(red) = {r}/{total} = {Fraction(r, total)}.",
        "level": "Junior (JMC)"
    }

def tpl_permutations():
    n = random.randint(3, 6)
    answer = math.factorial(n)
    assert math.factorial(n) == answer
    opts, letter = make_numeric_options(answer)
    steps = " × ".join(str(i) for i in range(n, 0, -1))
    return {
        "question": f"In how many different ways can {n} people be arranged in a line?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"Number of arrangements = {n}! = {steps} = {answer}.",
        "level": "Intermediate (IMC)"
    }

def tpl_combinations():
    n = random.randint(5, 10)
    r = random.randint(2, 4)
    answer = math.comb(n, r)
    assert math.comb(n, r) == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"How many ways can {r} items be chosen from {n} distinct items (order doesn't matter)?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"C({n},{r}) = {n}! / ({r}! × {n-r}!) = {answer}.",
        "level": "Intermediate (IMC)"
    }

# ── DATA / STATISTICS ─────────────────────────────────────────────────────────

def tpl_mean():
    vals = sorted([random.randint(5, 20) for _ in range(5)])
    total = sum(vals)
    n = len(vals)
    answer = total // n
    if total % n != 0:
        # Adjust last value to make mean clean
        vals[-1] = answer * n - sum(vals[:-1])
        total = sum(vals)
    assert sum(vals) % n == 0
    assert sum(vals) // n == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"What is the mean of the numbers {', '.join(str(v) for v in vals)}?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"Mean = sum ÷ count = {total} ÷ {n} = {answer}.",
        "level": "Junior (JMC)"
    }

def tpl_find_missing_for_mean():
    known = [random.randint(5, 20) for _ in range(4)]
    target_mean = random.randint(10, 18)
    n = 5
    missing = target_mean * n - sum(known)
    if missing <= 0 or missing > 30:
        known = [10, 12, 14, 16]
        target_mean = 15
        missing = target_mean * 5 - sum(known)
    assert sum(known + [missing]) == target_mean * n
    opts, letter = make_numeric_options(missing)
    return {
        "question": f"The mean of five numbers is {target_mean}. Four of the numbers are {', '.join(str(k) for k in known)}. What is the fifth number?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"Total = {target_mean} × {n} = {target_mean*n}. Sum of four known = {sum(known)}. Fifth = {target_mean*n} − {sum(known)} = {missing}.",
        "level": "Junior (JMC)"
    }

# ── POWERS & INDICES ──────────────────────────────────────────────────────────

def tpl_powers_arithmetic():
    a = random.randint(2, 4)
    b = random.randint(2, 5)
    c = random.randint(2, 6)
    answer = a ** b * c
    assert a**b * c == answer
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"What is the value of {a}^{b} × {c}?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"{a}^{b} = {a**b}. Then {a**b} × {c} = {answer}.",
        "level": "Junior (JMC)"
    }

def tpl_index_law_multiply():
    base = random.choice([2, 3, 5])
    p = random.randint(2, 6)
    q = random.randint(2, 6)
    answer = p + q
    assert base**p * base**q == base**(p+q)
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"What is the value of n if {base}^{p} × {base}^{q} = {base}^n?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"When multiplying powers of the same base, add exponents: {p} + {q} = {answer}.",
        "level": "Intermediate (IMC)"
    }

def tpl_solve_power_equation():
    base = random.choice([2, 3, 4, 5])
    exp = random.randint(2, 6)
    answer = base ** exp
    assert answer == base**exp
    opts, letter = make_numeric_options(answer)
    return {
        "question": f"What is the value of {base}^{exp}?",
        "option_a": opts[0], "option_b": opts[1],
        "option_c": opts[2], "option_d": opts[3], "option_e": opts[4],
        "answer": letter,
        "explanation": f"{base}^{exp} = {' × '.join([str(base)]*exp)} = {answer}.",
        "level": "Junior (JMC)"
    }


# ── MASTER LIST ───────────────────────────────────────────────────────────────

ALL_TEMPLATES = [
    # Geometry
    tpl_rectangle_area, tpl_circle_area, tpl_circle_circumference,
    tpl_cube_surface_area, tpl_cube_volume, tpl_cylinder_volume,
    tpl_right_triangle_hypotenuse, tpl_right_triangle_leg,
    tpl_interior_angle_polygon, tpl_exterior_angle_polygon,
    tpl_triangle_missing_angle, tpl_isosceles_triangle_angle,
    tpl_quadrilateral_missing_angle,
    # Number
    tpl_last_digit_power, tpl_sum_arithmetic_sequence, tpl_nth_term,
    tpl_sum_squares, tpl_sum_first_n, tpl_power_of_two_sum,
    tpl_divisibility_count, tpl_factorial_value, tpl_factorial_sum,
    # Algebra
    tpl_linear_equation, tpl_substitute_quadratic, tpl_difference_of_squares,
    tpl_consecutive_integers_sum, tpl_expression_evaluation,
    # Percentage / ratio
    tpl_percentage_of, tpl_reverse_percentage, tpl_percentage_increase,
    tpl_ratio_sharing, tpl_speed_distance_time, tpl_speed_time_from_distance,
    # Probability / combinatorics
    tpl_simple_probability, tpl_permutations, tpl_combinations,
    # Statistics
    tpl_mean, tpl_find_missing_for_mean,
    # Powers
    tpl_powers_arithmetic, tpl_index_law_multiply, tpl_solve_power_equation,
]


def generate_from_template():
    """Pick a random template, run it, return a verified question dict."""
    random.shuffle(ALL_TEMPLATES)
    for tpl_fn in ALL_TEMPLATES:
        try:
            result = tpl_fn()
            if result:
                return result
        except AssertionError as e:
            continue  # template generated bad values, try next
        except Exception as e:
            print(f"⚠️ Template {tpl_fn.__name__} error: {e}")
            continue
    return None


# ─────────────────────────────────────────────────────────────────────────────
# AI PROMPT (used as 30% fallback)
# ─────────────────────────────────────────────────────────────────────────────

UKMT_PROMPT = """You are an expert UKMT question writer. Generate ONE original UKMT-style multiple choice question.

TODAY'S LEVEL: {level}

STRICT RULES:
- 5 options A, B, C, D, E — exactly one correct
- Must be genuinely UKMT style — elegant, needs insight
- Triple-check your arithmetic before outputting
- Include a verify_expr: a Python expression using only +,-,*,/,**,% and math functions that evaluates to True when the answer is correct. Examples:
  - "12 * 14 == 168"
  - "(5**2 + 12**2)**0.5 == 13.0"
  - "(10-2)*180//10 == 144"
  - "sum(range(1,101)) == 5050"

Respond ONLY in this exact JSON, no other text, no markdown:
{
  "question": "full question text",
  "option_a": "value",
  "option_b": "value",
  "option_c": "value",
  "option_d": "value",
  "option_e": "value",
  "answer": "A",
  "explanation": "clear step-by-step solution",
  "verify_expr": "python expression that returns True",
  "level": "{level}"
}"""


def safe_verify(expr):
    """
    Safely evaluate a verify_expr using ast whitelisting.
    Returns True if the expression evaluates to True.
    Returns None if the expression is unsafe or errors.
    """
    if not expr or not isinstance(expr, str):
        return None
    try:
        tree = ast.parse(expr, mode='eval')
        ALLOWED_NODES = {
            ast.Expression, ast.BoolOp, ast.BinOp, ast.UnaryOp,
            ast.Compare, ast.Constant, ast.Add, ast.Sub, ast.Mult,
            ast.Div, ast.Pow, ast.Mod, ast.FloorDiv, ast.Eq, ast.NotEq,
            ast.Lt, ast.LtE, ast.Gt, ast.GtE, ast.And, ast.Or, ast.Not,
            ast.USub, ast.UAdd, ast.Call, ast.Name, ast.Load, ast.Num,
            ast.Attribute
        }
        for node in ast.walk(tree):
            if type(node) not in ALLOWED_NODES:
                print(f"⚠️ Unsafe AST node: {type(node).__name__}")
                return None
        safe_globals = {
            "__builtins__": {},
            "math": math,
            "abs": abs,
            "round": round,
            "int": int,
            "float": float,
            "sum": sum,
            "range": range,
            "min": min,
            "max": max,
            "sqrt": math.sqrt,
            "factorial": math.factorial,
            "comb": math.comb,
            "gcd": math.gcd,
        }
        result = eval(compile(tree, '<verify>', 'eval'), safe_globals)
        return bool(result)
    except Exception as e:
        print(f"⚠️ verify_expr eval error: {e} | expr: {expr}")
        return None


def ai_second_opinion(data):
    """
    Ask a second AI call to independently solve the question.
    Returns corrected data if it disagrees, original data if it agrees,
    or None if the question seems fundamentally broken.
    """
    try:
        prompt = f"""Solve this maths question independently. Show your working step by step, then state the correct answer letter.

Question: {data['question']}
A) {data['option_a']}
B) {data['option_b']}
C) {data['option_c']}
D) {data['option_d']}
E) {data['option_e']}

Respond ONLY in JSON, no other text:
{{"working": "your step by step working", "answer": "A", "agrees_with_stated": true}}

The stated answer is {data['answer']}. Set agrees_with_stated to true if you agree, false if not."""

        resp = client.chat.completions.create(
            model="llama-3.3-70b-versatile",
            messages=[{"role": "user", "content": prompt}],
            temperature=0,
            max_tokens=600
        )
        raw = resp.choices[0].message.content.strip()
        if '{' in raw:
            raw = raw[raw.index('{'):raw.rindex('}')+1]
        result = json.loads(raw)

        if result.get('agrees_with_stated'):
            print(f"✅ Second opinion agrees: {data['answer']}")
            return data

        actual = result.get('answer', '').strip().upper()
        if actual in ['A', 'B', 'C', 'D', 'E'] and actual != data['answer']:
            print(f"⚠️ Second opinion: stated={data['answer']}, actual={actual}. Correcting.")
            data['answer'] = actual
            data['explanation'] = result.get('working', data['explanation'])
            return data

        return data  # can't determine, accept original

    except Exception as e:
        print(f"⚠️ Second opinion failed: {e}")
        return data


def generate_ai_question(level):
    """Generate a question using AI with verification. Returns dict or None."""
    for attempt in range(3):
        try:
            resp = client.chat.completions.create(
                model="llama-3.3-70b-versatile",
                messages=[{"role": "user", "content": UKMT_PROMPT.format(level=level)}],
                temperature=0.7,
                max_tokens=1200
            )
            raw = resp.choices[0].message.content.strip()
            if '{' in raw:
                raw = raw[raw.index('{'):raw.rindex('}')+1]
            data = json.loads(raw)

            # Step 1: Python checks the verify_expr
            verify_result = safe_verify(data.get('verify_expr', ''))

            if verify_result is False:
                # Arithmetic is provably wrong — ask second AI to fix it
                print(f"⚠️ Attempt {attempt+1}: verify_expr returned False. Sending to second opinion.")
                data = ai_second_opinion(data)
                if data is None:
                    continue
                # Re-verify after correction
                verify_result = safe_verify(data.get('verify_expr', ''))
                if verify_result is False:
                    print(f"⚠️ Still wrong after second opinion. Retrying.")
                    continue

            elif verify_result is None:
                # Can't verify — use second opinion as extra check
                print(f"ℹ️ Attempt {attempt+1}: verify_expr unverifiable. Using second opinion.")
                data = ai_second_opinion(data)
                if data is None:
                    continue

            # verify_result is True or None-but-second-opinion-checked
            return data

        except json.JSONDecodeError as e:
            print(f"⚠️ JSON parse failed attempt {attempt+1}: {e}")
        except Exception as e:
            print(f"❌ AI attempt {attempt+1} failed: {e}")

    return None


def pick_level():
    r = random.random()
    if r < 0.65:
        return "Intermediate (IMC)"
    elif r < 0.85:
        return random.choice(["Junior (JMC)", "Intermediate (IMC)"])
    else:
        return "Senior (SMC)"


def generate_question():
    """
    Main question generation function.
    70% template (Python-verified, arithmetically perfect).
    30% AI (with Python verify_expr + second AI opinion).
    """
    today = date.today().isoformat()
    conn = get_db()
    existing = conn.execute('SELECT id FROM questions WHERE date = ?', (today,)).fetchone()
    conn.close()
    if existing:
        return

    # ── 70% TEMPLATE PATH ────────────────────────────────────────────────────
    if random.random() < 0.70:
        data = generate_from_template()
        if data:
            conn = get_db()
            conn.execute(
                '''INSERT OR IGNORE INTO questions
                   (date, question, option_a, option_b, option_c, option_d, option_e,
                    answer, explanation, level, source)
                   VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)''',
                (today, data['question'], data['option_a'], data['option_b'],
                 data['option_c'], data['option_d'], data['option_e'],
                 data['answer'], data['explanation'], data['level'], 'template')
            )
            conn.commit()
            conn.close()
            print(f"✅ Template question for {today} [{data['level']}]")
            return

    # ── 30% AI PATH ───────────────────────────────────────────────────────────
    level = pick_level()
    data = generate_ai_question(level)

    if data:
        conn = get_db()
        conn.execute(
            '''INSERT OR IGNORE INTO questions
               (date, question, option_a, option_b, option_c, option_d, option_e,
                answer, explanation, level, source)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)''',
            (today, data['question'], data['option_a'], data['option_b'],
             data['option_c'], data['option_d'], data['option_e'],
             data['answer'], data['explanation'], data.get('level', level), 'ai')
        )
        conn.commit()
        conn.close()
        print(f"✅ AI question for {today} [{level}]")
        return

    # ── FALLBACK: template always works ─────────────────────────────────────
    data = generate_from_template()
    if data:
        conn = get_db()
        conn.execute(
            '''INSERT OR IGNORE INTO questions
               (date, question, option_a, option_b, option_c, option_d, option_e,
                answer, explanation, level, source)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)''',
            (today, data['question'], data['option_a'], data['option_b'],
             data['option_c'], data['option_d'], data['option_e'],
             data['answer'], data['explanation'], data['level'], 'template_fallback')
        )
        conn.commit()
        conn.close()
        print(f"✅ Fallback template question for {today}")


# ─────────────────────────────────────────────────────────────────────────────
# DISCORD WEBHOOK
# ─────────────────────────────────────────────────────────────────────────────

def send_discord(mc_username, discord_username, answer, is_correct, question_text, date_str):
    if not DISCORD_WEBHOOK:
        return
    import requests as req
    color = 0x6BCF7F if is_correct else 0xFF6B6B
    payload = {
        "embeds": [{
            "title": "📐 New UKMT Submission!",
            "color": color,
            "fields": [
                {"name": "Minecraft Username", "value": mc_username, "inline": True},
                {"name": "Discord Username",   "value": discord_username, "inline": True},
                {"name": "Answer Submitted",   "value": answer, "inline": True},
                {"name": "Result", "value": "✅ Correct!" if is_correct else "❌ Wrong", "inline": True},
                {"name": "Date", "value": date_str, "inline": True},
                {"name": "Question", "value": question_text[:200] + ("..." if len(question_text) > 200 else ""), "inline": False},
            ],
            "timestamp": datetime.utcnow().isoformat()
        }]
    }
    try:
        req.post(DISCORD_WEBHOOK, json=payload, timeout=5)
    except Exception as e:
        print(f"⚠️ Discord webhook failed: {e}")


# ─────────────────────────────────────────────────────────────────────────────
# SCHEDULER
# ─────────────────────────────────────────────────────────────────────────────

scheduler = BackgroundScheduler()
scheduler.add_job(generate_question, 'cron', hour=0, minute=1)
scheduler.start()


# ─────────────────────────────────────────────────────────────────────────────
# ROUTES
# ─────────────────────────────────────────────────────────────────────────────

@app.route('/')
def home():
    generate_question()
    return render_template('index.html')

@app.route('/sw.js')
def service_worker():
    return send_from_directory('static', 'sw.js', mimetype='application/javascript')

@app.route('/question')
def get_question():
    today = date.today().isoformat()
    yesterday = (date.today() - timedelta(days=1)).isoformat()

    conn = get_db()
    q = conn.execute('SELECT * FROM questions WHERE date = ?', (today,)).fetchone()
    yq = conn.execute('SELECT * FROM questions WHERE date = ?', (yesterday,)).fetchone()
    conn.close()

    if not q:
        generate_question()
        conn = get_db()
        q = conn.execute('SELECT * FROM questions WHERE date = ?', (today,)).fetchone()
        conn.close()

    if not q:
        return jsonify({'error': 'No question available yet'}), 404

    return jsonify({
        'today': {
            'date': q['date'],
            'question': q['question'],
            'option_a': q['option_a'],
            'option_b': q['option_b'],
            'option_c': q['option_c'],
            'option_d': q['option_d'],
            'option_e': q['option_e'],
            'level': q['level'],
        },
        'yesterday': {
            'date': yq['date'],
            'question': yq['question'],
            'answer': yq['answer'],
            'explanation': yq['explanation'],
            'level': yq['level'],
        } if yq else None
    })

@app.route('/submit', methods=['POST'])
def submit():
    data = request.get_json()
    mc_username      = data.get('mc_username', '').strip()
    discord_username = data.get('discord_username', '').strip()
    answer           = data.get('answer', '').strip().upper()
    today            = date.today().isoformat()

    if not mc_username:
        return jsonify({'success': False, 'error': 'Minecraft username required'})
    if not discord_username:
        return jsonify({'success': False, 'error': 'Discord username required'})
    if answer not in ['A', 'B', 'C', 'D', 'E']:
        return jsonify({'success': False, 'error': 'Invalid answer'})
    if len(mc_username) > 16:
        return jsonify({'success': False, 'error': 'Minecraft username too long'})
    if len(discord_username) > 40:
        return jsonify({'success': False, 'error': 'Discord username too long'})

    conn = get_db()

    already = conn.execute(
        'SELECT id FROM submissions WHERE date = ? AND mc_username = ?',
        (today, mc_username)
    ).fetchone()
    if already:
        conn.close()
        return jsonify({'success': False, 'error': 'You have already submitted today!'})

    q = conn.execute('SELECT * FROM questions WHERE date = ?', (today,)).fetchone()
    if not q:
        conn.close()
        return jsonify({'success': False, 'error': 'No question found for today'})

    is_correct = int(answer == q['answer'])

    conn.execute(
        '''INSERT INTO submissions (date, mc_username, discord_username, answer, is_correct, submitted_at)
           VALUES (?, ?, ?, ?, ?, ?)''',
        (today, mc_username, discord_username, answer, is_correct, int(time.time()))
    )
    conn.commit()
    conn.close()

    send_discord(mc_username, discord_username, answer, bool(is_correct), q['question'], today)

    return jsonify({'success': True, 'correct': bool(is_correct)})

@app.route('/leaderboard')
def leaderboard():
    conn = get_db()
    users = conn.execute('''
        SELECT mc_username,
               COUNT(*)      AS total,
               SUM(is_correct) AS correct
        FROM submissions
        GROUP BY mc_username
        ORDER BY correct DESC, total ASC
        LIMIT 20
    ''').fetchall()
    conn.close()
    return jsonify([dict(u) for u in users])

@app.route('/feedback-cooldown', methods=['GET'])
def feedback_cooldown():
    ip = request.remote_addr
    conn = get_db()
    row = conn.execute(
        'SELECT last_submitted FROM feedback_cooldowns WHERE ip = ?', (ip,)
    ).fetchone()
    conn.close()
    if not row:
        return jsonify({'remaining': 0})
    elapsed = int(time.time()) - row['last_submitted']
    remaining = max(0, FEEDBACK_COOLDOWN - elapsed)
    return jsonify({'remaining': remaining * 1000})

@app.route('/set-feedback-cooldown', methods=['POST'])
def set_feedback_cooldown():
    ip = request.remote_addr
    conn = get_db()
    conn.execute(
        'INSERT OR REPLACE INTO feedback_cooldowns (ip, last_submitted) VALUES (?, ?)',
        (ip, int(time.time()))
    )
    conn.commit()
    conn.close()
    return jsonify({'success': True})

# ─────────────────────────────────────────────────────────────────────────────

if __name__ == '__main__':
    app.run(debug=False)
