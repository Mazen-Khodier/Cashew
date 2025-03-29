from itertools import product
from collections import defaultdict
import sys
import pexpect
from time import time

time0 = time()
membership_time = 0


BASE = 2 # 2 for Binary, 3 for Ternay, etc.
LENGTH = 2 # Morphism Length
MAX_LENGTH = BASE**LENGTH

# correct_file = "eqtm/eqtm.txt"
walnut_dir = "./" #directory where "walnut.sh" exists, ends with "/"
walnut_process = pexpect.spawn(walnut_dir+"walnut.sh")
walnut_process.expect(r"\[Walnut\]\$")


orig_stdout = sys.stdout
log_file = "log.txt"
# f = open(log_file, 'w')
# sys.stdout = f

# Add continuation

# Inputs for the target automaton
input_letters = ["i", "j", "n"]
# Ensure lexicographic ordering
input_letters.sort()   
n_inputs = len(input_letters)
mem_query_info = {"count": 0, "longest": 0}

# Extra inputs for the membership automaton (if any)
extra_letters = ["t", "u", "v"]
member_letters = sorted(input_letters + extra_letters)
n_member = len(input_letters)
#membership_query = 'def member "(t<n) & BS[i+t]!=BS[j+t]":'
membership_query = 'def member "t<n & u=i+t & v=j+t & BS[u]!=BS[v]":'


# Tested sequentially for counterexamples.
# It is assumed that the counterexample is the accepted string itself without any needed modifications
# e.g: If the string (i_0, j_0, n_0) is accepted, then (i_0, j_0, n_0) is the counterexample, not (i_0, j_0, n_0 - 1)
# Result automaton should be called "conj"
counterexample_tests = [
    'def counter1 "~$conj(i,j,0)":',
    'def counter2 "n>0 & $conj(i,j,n) & BS[i+n-1]!=BS[j+n-1]":',
    'def counter3 "$conj(i,j,n-1) & BS[i+n-1]=BS[j+n-1] & ~$conj(i,j,n)":'
    ]

# For any initializations needed at the beginning. e.g: Defining a morphism
startup_commands = [
    'morphism g "0->01 1->10":',
    'promote TM g:'
    ]
startup_commands += [membership_query]
   
membership_hash = defaultdict()
eps = ""
empty = tuple([eps for i in range(n_inputs)])
temp = ["0", "1"]
S = [empty]
E = S[:]
A = S + [tuple(map(str, a)) for a in product(temp, repeat=n_inputs)]
Tables = []

add = lambda l1, l2: tuple([x+y for x, y in zip(l1, l2)])

def run_walnut(command):
    walnut_process.sendline(command)
    walnut_process.expect(r"\[Walnut\]\$")  # Look for the expected prompt
    response = walnut_process.before.decode('utf-8').strip()
    #print(command)
    #print(response)
    return response
    
for command in startup_commands:
    run_walnut(command)

def is_member(string):
    t0 = time()
    global membership_time
    global membership_hash
    global mem_query_info
    mem_query_info["count"] += 1
    mem_query_info["longest"] = max(mem_query_info["longest"], len(string[0]))
    try:
        return membership_hash[string]
    except:
        commands = [f'reg x{i} msd_2 "0*{string[i]}":' for i in range(n_inputs)]
        for command in commands:
            run_walnut(command)
        matching = " ".join([f"$x{i}({input_letters[i]}) &" for i in range(n_inputs)])
        command_1 = f'def tmp "{matching} $member({", ".join(member_letters)})":'
        run_walnut(command_1)
        response = run_walnut("test tmp 1:")
        res = response[-1] != "]"
        membership_hash[string] = res       
        t1 = time()
        membership_time += t1-t0
        return res

# Fill Table
T_temp = defaultdict()
for a in A:
    T_temp[a] = defaultdict()
    if a == (eps, eps, eps):
        T_temp[a][a] = True
        continue
    T_temp[a][(eps, eps, eps)] = is_member(a)
Tables.append(T_temp)

def is_consistent():
    global mem_count
    mem_count = 0
    for i in range(len(S) - 1):
        for j in range(i+1, len(S)):
            s1 = S[i]
            s2 = S[j]
            if Tables[-1][tuple(s1)] == Tables[-1][tuple(s2)]:
                res = children(i, j)
                if not res[0]:
                    return False, res[1]
    return True, None

# What if not in table? Ignored for now
def children(i, j):
    for k in range(len(A)):
        for l in range(len(E)):
            a, e = A[k], E[l]
            ae = add(a, e)
            temp1 = add(S[i], ae)
            temp2 = add(S[j], ae)
            if temp1 == empty:
                r1 = True
            else:
                r1 = is_member(temp1)
            if temp2 == empty:
                r2 = True
            else:
                r2 = is_member(temp2)
            if r1 != r2:
                    return False, (k, l, i, j)
    return True, None
 
# What if not in table? Maybe impossible
def is_closed():
    global mem_count
    mem_count = 0
    for i in range(len(S)):
        for j in range(len(A)):
            sa = add(S[i], A[j])
            if sa in S:
                pass
            else:
                res = False
                for k in range(len(S)):
                    if Tables[-1][tuple(sa)] == Tables[-1][tuple(S[k])]:
                        res = True
                        break
                if not res:
                    return False, (i, j)
    return True, None

def extend_E():
    T_last = Tables[-1]
    T_temp = T_last.copy()
    e = E[-1]
    SA = [key for key in T_temp]
    for sa in SA:
        sae = add(sa, e)
        T_temp[sa][e] = is_member(sae)
    Tables.append(T_temp)
    return

def extend_S(l):
    T_last = Tables[-1]
    T_temp = T_last.copy()
    for k in range(l, 0, -1):
        s = S[-k]
        for i in range(len(E)):
            for j in range(len(A)):
                sa = add(s, A[j])
                if sa not in T_temp:
                    T_temp[sa] = defaultdict(dict)
                e = E[i]
                sae = add(sa, e)
                T_temp[sa][e] = is_member(sae)
    # print(T_temp)
    Tables.append(T_temp)
    return

def make_conj():
    Qr = []
    Qs = []
    F = []
    for i in range(len(S)):
        s = S[i]
        row = Tables[-1][tuple(s)]
        if row not in Qr:
            Qr.append(row)
            Qs.append(s)
        if Tables[-1][tuple(s)][(eps, eps, eps)] == 1:
            if row not in F:
                F.append(Qr.index(row))
    trans_func = defaultdict()
    for i in range(len(Qs)):
        trans_func[i] = defaultdict()
        s = Qs[i]
        for j in range(len(A)):
            a = A[j]
            sa = add(s, a)
            row = Tables[-1][sa]
            out = Qr.index(row)
            trans_func[i][a] = out

    walnut_automaton = f"msd_{LENGTH} " * 3 + "\n"
    for i in range(len(Qs)):
        walnut_automaton += f"\n{i} {int(i in F)}\n"
        for j in range(1, len(A)):
            a = A[j]
            line = f"{' '.join(a)} -> {trans_func[i][a]}\n"
            walnut_automaton += line
    return walnut_automaton

def check_tests(conj):
    automata_dir = walnut_dir + "Automata Library/conj.txt"
    with open(automata_dir, "w") as conj_file:
        conj_file.write(conj)
    for t in range(len(counterexample_tests)):
        test = counterexample_tests[t]
        run_walnut(test)
        name = test.split()[1]
        result = run_walnut(f"test {name} 1:")
        if result[-1] == ']':
            text = result.split('\n')[-1]
            segments = text.strip('[]').split('][')
            arrays = [segment.split(', ') for segment in segments]
            counter_ex = tuple(["".join(arrays[j][i] for j in range(len(arrays))) for i in range(n_inputs)])
            print("Counterexample found!!!\n", counter_ex)
            return False, counter_ex
    return True, 0

def test_conj():
    conj = make_conj()
    print(conj)
    res = check_tests(conj)
    if res[0]:
        return True, None
    return False, res[1]

def parse_automaton(data):
    lines = data.strip().split("\n")
    num_inputs = lines[0].count("msd_2")  # Number of input bits

    func = defaultdict()
    active_states = set()

    i = 1
    while i < len(lines):
        if not lines[i].strip():
            i += 1
            continue

        # Read state and active flag
        state_info = lines[i].split()
        state = int(state_info[0])
        if state_info[1] == "1":
            active_states.add(state)

        func[state] = defaultdict()
        i += 1

        # Read transitions
        while i < len(lines) and "->" in lines[i]:
            parts = lines[i].split(" -> ")
            input_tuple = tuple(parts[0].split())  # Convert to tuple of strings
            next_state = int(parts[1])
            func[state][input_tuple] = next_state
            i += 1

    return func, sorted(active_states)

def run_automaton(A, bin_string):
    trans_func, accept = parse_automaton(A)
    # print(bin_string)
    current_state = 0
    for i in range(len(bin_string[0])):
        char = tuple([bin_string[j][i] for j in range(len(bin_string))])
        try:
            current_state = trans_func[current_state][char]
        except:
            return False
    return current_state in accept

# Group S first when printing
def print_table():
    data = Tables[-1]

    inner_keys = {key for inner in data.values() for key in inner.keys()}
    headers = ['Name'] + sorted(inner_keys)
    rows = []
    for name, attrs in data.items():
        row = [str(name)] + [str(attrs.get(key, '')) for key in headers[1:]]
        rows.append(row)
    str_headers = [str(h) for h in headers]
    column_widths = [
        max(len(str_headers[i]), *(len(row[i]) for row in rows))
        for i in range(len(headers))
    ]
    format_str = '  '.join(f'{{:<{width}}}' for width in column_widths)
    print(format_str.format(*str_headers))
    for row in rows:
        print(format_str.format(*row))

iteration = 0
while True:
    #print("Press Enter for next iteration.")
    # input()

    iteration += 1
    print("Iteration: ", iteration)
    print_table()
    print("S = ", S)
    print("E = ", E)

    print("Checking consistency...", end=" ")
    res = is_consistent()
    print(f"{mem_query_info['count']} membership queries, longest of length {mem_query_info['longest']}.")
    if not res[0]:
        k, l, i, j = res[1]
        ae = add(A[k], E[l])
        E.append(ae)
        print("Table is NOT consistent!\nExtending E")
        print(f"s1 = {S[i]}, s2 = {S[j]}, a = {A[k]}, e = {E[l]}")
        extend_E()
        continue
    print("Table is consistent.\n") 

    print("Checking closed property...", end=" ")
    res = is_closed()
    print(f"{mem_query_info['count']} membership queries, longest of length {mem_query_info['longest']}.")
    if not res[0]:
        i, j = res[1]
        sa = add(S[i], A[j])
        S.append(sa)
        print("Table is NOT closed!\nExtending S:")
        print(f"s = {S[i]}, a = {A[j]}")
        extend_S(1)
        continue
    print("Table is closed.\n")
    
    print("\nForming conjecture automaton:\n")
    res = test_conj()
    if not res[0]:
        t = res[1]
        print("Adding counterexample to the table...")
        # t1 = input()
        # t2 = input()
        # t3 = input()
        # t = (t1, t2, t3)
        counter = 0
        for i in range(1, len(t[0])+1):
            prefix = tuple([t[j][:i] for j in range(len(t))])
            # print(t)
            # print(prefix)
            # print(S)
            if prefix in S:
                pass
            else:
                S.append(prefix)
                counter += 1
        # print(S)
        extend_S(counter)
    else:
        print("DONE !")
        break
        
time1 = time()

print("total time = ", time1-time0)
print("membership time = ", membership_time)


walnut_process.terminate()
sys.stdout = orig_stdout
f.close()




'''
eval check1 "?msd_k Ai,j $eqfac(i,j,0)":
eval check2 "?msd_k Ai,j,n $eqfac(i,j,n) => ($eqfac(i,j,n+1) <=> X[i+n]=X[j+n])":
eval check3 "?msd_k Ai,j,n $eqfac(i,j,n+1) => $eqfac(i,j,n)":

If all three of these checks return TRUE, then $eqfac is correct (by induction on n).
If any one returns FALSE, we can find a counterexample with

def counter1 "?msd_k ~$eqfac(i,j,0)":
def counter2 "?msd_k $eqfac(i,j,n) & ~($eqfac(i,j,n+1) <=> X[i+n]=X[j+n])":
def counter3 "?msd_k ~($eqfac(i,j,n+1) => $eqfac(i,j,n))":
'''

# def generate(morph, iterations=1000):
#     string = "0"
#     i = 0

#     while i < iterations:
#         temp = []
#         for i in range(len(string)):
#             # if i % 1000000 == 0:
#                 # print(i)
#             temp.append(morph[string[i]])
#         string = "".join(temp)
#     return string

# fixed = generate(morph)
# check_eq = lambda w, i, j, n: w[i:i+n] == w[j:j+n]

# def counter_ex(conj, correct):
#     n = 0
#     while True:
#         n += 1
#         binary_strings = [format(i, f'0{n}b') for i in range(2**n)]
#         for triplet in product(binary_strings, repeat=3):
#             if run_automaton(conj, triplet) != run_automaton(correct, triplet):
#                 print("Counterexample found!!!:", triplet)
#                 return triplet

# def test_conj():
#     conj = make_conj()
#     print(conj)
#     with open(correct_file, "r") as file:
#         correct = file.read()
#     if conj == correct:
#         return True, None
#     return False, counter_ex(conj, correct)
