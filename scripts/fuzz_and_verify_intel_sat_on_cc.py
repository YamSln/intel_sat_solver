import os
import subprocess
import tempfile

instaces_directory = 'cardinality_constraints_instances'
solver_directory = 'x64\\Release'
solver_name = 'topor.exe'
fuzzer_directory = 'third_party\\cnfuzzdd2013'
fuzzer_name = 'cnfuzz_card.exe'

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
    return "UNSAT"

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

solver = get_relative(f'{solver_directory}\\{solver_name}')
fuzzer = get_relative(f'{fuzzer_directory}\\{fuzzer_name}')

if __name__ == '__main__':
    while True:
        with tempfile.NamedTemporaryFile(delete=False) as temp_file:
            subprocess.run(fuzzer, stdout=temp_file, text=True)
            result = subprocess.run(f'{solver} {temp_file.name}', capture_output=True, text=True)
            assignment = get_assignment_from_result(result.stdout.splitlines())
            constraints = read_cardinality_constraints_from_file(temp_file.name)
        if assignment == "UNSAT":
            print("UNSAT")
            continue
        for i, constraint in enumerate(constraints):
            if not check_sat(assignment, vars=constraint['vars'], predicate=constraint['pred'], k=constraint['k']):
                print(f'\n\tConstraint number {i+1} is not satisfied!', end='')
                exit(1)
        print("**** Pass ****")