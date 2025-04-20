import os
import subprocess
import tempfile
import msvcrt
import threading
import time
import shutil

solver_directory = 'x64\\Release'
solver_name = 'topor.exe'
fuzzer_directory = 'third_party\\cnfuzzdd2013'
fuzzer_name = 'cnfuzz_card.exe'
run_duration_sec = 60

def get_relative(directory_name):
    return os.path.join('..', directory_name)

def read_cardinality_constraints_from_file(file_path):
    
    def read_constraint_line(line):
        constraint = line.strip()[1:].strip().split()
        return {'vars': [int(var) for var in constraint[-4::-1]],
                'pred': constraint[-3],
                'k': int(constraint[-2])}
        
    constraints = []
    with open(file_path, 'r') as file:
        for line in file:
            if line.strip().startswith('d'):
                constraints.append(read_constraint_line(line))
    return constraints

def read_cardinality_constraints_from_cnf_string(cnf_string):
    
    def read_constraint_line(line):
        constraint = line.strip()[1:].strip().split()
        return {'vars': [int(var) for var in constraint[-4::-1]],
                'pred': constraint[-3],
                'k': int(constraint[-2])}
        
    constrains = []
    for line in cnf_string:
        if line.strip().startswith('d'):
            constrains.append(read_constraint_line(line))
    return constrains

def get_assignment_from_result(result_out):
    for line in result_out:
        if line.strip().startswith('v'):
            return [int(var) for var in line.strip().split()[1:]][:-1]
        if line.strip().startswith('s UNSATISFIABLE'):
            return "UNSAT"
    return "ERROR"

def check_sat(assignment, vars, predicate, k):
    num_sat = sum([vars[i] in assignment for i in range(len(vars))])
    if predicate == '<':
        return num_sat < k
    if predicate == '<=':
        return num_sat <= k
    if predicate in ['=', '==']:
        return num_sat == k
    if predicate == '>=':
        return num_sat >= k
    if predicate == '>':
        return num_sat > k
    raise ValueError("Invalid predicate at SAT check")

def print_stats(stats):
    print()
    print(f'{'*' * 10} STATS {'*' * 10}')
    print(f'Solver: {solver} | Fuzzer: {fuzzer}')
    print(f'Run duration (sec): {round(stats["END"] - stats["START"], 2)}')
    print(f'SAT / UNSAT Ratio: {stats["SAT"]}/{stats["UNSAT"]}.')
    print(f'The solver returned {stats["ERROR"]} times with an error.')
    print()
    
    
if __name__ == '__main__':
    
    solver = get_relative(f'{solver_directory}\\{solver_name}')
    fuzzer = get_relative(f'{fuzzer_directory}\\{fuzzer_name}')
    key_pressed = False

    def wait_for_keypress():
        global key_pressed
        while True:
            if msvcrt.kbhit():
                key_pressed = True
                break

    listener_thread = threading.Thread(target=wait_for_keypress)
    listener_thread.daemon = True
    listener_thread.start()
    
    stats = {"SAT": 0, "UNSAT": 0, "ERROR": 0, "START": 0, "END": 0}
    start_time = time.time()
    stats["START"] = start_time
    print (f'Fuzzing loop started, duration: {run_duration_sec} sec.')
    while True:
        if key_pressed:
            print("Key was pressed! Exiting fuzzing loop.")
            stats["END"] = time.time()
            break
        if time.time() - start_time > run_duration_sec:
            print("Timer expired! Exiting fuzzing loop.")
            stats["END"] = time.time()
            break
        
        with tempfile.NamedTemporaryFile(delete=False) as temp_file:
            subprocess.run(fuzzer, stdout=temp_file, text=True)
            result = subprocess.run(f'{solver} {temp_file.name}', capture_output=True, text=True)
            assignment = get_assignment_from_result(result.stdout.splitlines())
            constraints = read_cardinality_constraints_from_file(temp_file.name)
            if assignment == "UNSAT":
                stats["UNSAT"] += 1
                # print("UNSAT")
                continue
            if assignment == "ERROR":
                stats["ERROR"] += 1
                # print("ERROR")
                continue
            stats["SAT"] += 1
            for i, constraint in enumerate(constraints):
                if not check_sat(assignment, vars=constraint['vars'], predicate=constraint['pred'], k=constraint['k']):
                    print(f'Constraint number {i+1} is not satisfied!')
                    print(f'\n\td {" ".join(str(var) for var in constraint['vars'])} {constraint['pred']} {constraint['k']}\n')
                    input_file_name = "last_run_input.txt"
                    print(f'You can view the input for this run in: {input_file_name}')
                    with open(temp_file.name, 'r') as source, open(input_file_name, 'w') as dest:
                        shutil.copyfileobj(source, dest)
                    print()
                    exit(1)
        # print("**** Pass ****")
    print_stats(stats)