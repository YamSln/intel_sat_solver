import os
import subprocess

instaces_directory = 'cardinality_constraints_instances'
solver_directory = 'x64\\Release'
solver_name = 'topor.exe'

def get_relative(directory_name):
    return os.path.join('..', directory_name)

def read_cardinality_constraints_from_files(directory_name):
    
    def read_constraint_line(line):
        constraint = line.strip()[1:].strip().split()
        return {'vars': [int(var) for var in constraint[-4::-1]],
                'pred': constraint[-3],
                'k': int(constraint[-2])}
        
    cnf_directory = get_relative(directory_name)
    constraints_dict = {}
    for filename in os.listdir(cnf_directory):
        if filename.endswith('.cnf'):
            file_path = os.path.join(cnf_directory, filename)
            with open(file_path, 'r') as file:
                constraints_dict[filename] = []
                for line in file:
                    if line.strip().startswith('d'):
                        constraints_dict[filename].append(read_constraint_line(line))
    return constraints_dict

def get_assignment_from_result(result_out):
    for line in result_out:
        if line.strip().startswith('v'):
            return [int(var) for var in line.strip().split()[1:]][:-1]
    raise ValueError("Solver output does not contain an assignment")

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
     

instances = read_cardinality_constraints_from_files(instaces_directory)
solver = get_relative(f'{solver_directory}\\{solver_name}')
test_results = {}

if __name__ == '__main__':
    for file_name, constraints_data in instances.items():
        # Run the solver with the file location as an argument
        arg = get_relative(f'{instaces_directory}\\{file_name}')
        result = subprocess.run(f'{solver} {arg}', capture_output=True, text=True)
        assignment = get_assignment_from_result(result.stdout.splitlines())
        
        print(f'{file_name}: ', end='')
        sat = True
        for i, constraint in enumerate(constraints_data):
            if not check_sat(assignment, vars=constraint['vars'], predicate=constraint['pred'], k=constraint['k']):
                print(f'\n\tConstraint number {i+1} is not satisfied!', end='')
                sat = False
        if sat:
            print("Passed")
        else:
            print()