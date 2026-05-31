import os
import subprocess
import re
import generate_case

def run_case(a_case, b_case, n, db_manager, timeout_seconds):
    idp_content = generate_case.generate_case(a_case, b_case, n)
    with open("test_case.idp", "w") as file:
        file.write(idp_content)
    result = f'{a_case},{b_case},{n},{db_manager},'
    try:
        proc = subprocess.Popen(
            ["sudo", "-S",
             "/home/nigel/.cache/pypoetry/virtualenvs/duckdbdep-9GR9n2aE-py3.12/bin/python3.12", "idp-z3-db.py",
             "test_case.idp", db_manager],
            cwd="./", stdout=subprocess.PIPE).communicate(input=b'inputPassword\n', timeout=timeout_seconds)
        res = proc[0]
        print(res)
        res_str = res.decode("utf-8")
        all_numbers = re.findall(r"(?:Parse|Ground|Solve):\s*([\d.]+)", res_str)
        parse = float(all_numbers[0])
        ground = float(all_numbers[1])
        solve = float(all_numbers[2])
        total = parse+ground+solve
        size = os.path.getsize('log') // 1024
        return result + f'{total},{parse},{ground},{solve},{size}'
    except subprocess.TimeoutExpired:
        return result + ',,,,,timeout'
    except Exception as e:
        return result + f',,,,,error:{e}'

def run_case_batch(a_case, b_case, db_manager, until, max_runs, function):
    timed_out = False
    i = 1
    results = []
    while not timed_out and i <= max_runs:
        n = function(i)
        print("Starting to run ", a_case, b_case, n, db_manager)
        result = run_case(a_case, b_case, n, db_manager, until)
        results.append(result)
        if 'timeout' in result:
            timed_out = True
        i += 1
    print()
    print('A-case,B-case,n,db_manager,total,parsing,grounding,solving,grounding_size(kb),error')
    for res in results:
        print(res)

def square_times_ten(i):
    return 10*i**2
def by_10(i):
    return i*10
def by_100(i):
    return i*100
def powers_ten(i):
    return 10**(i)

run_case_batch('A3','Bs','sqlite', 600, 15, square_times_ten)