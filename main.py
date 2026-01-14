from itertools import product
from collections import defaultdict, deque
from functools import reduce
import sys
import pexpect
from time import time

time0 = time()
membership_time = 0


# 2 for Binary, 3 for Ternay, etc. fib, trib
BASE = "2"
word = "BS"
method = "reg" # Current options: "reg", "instance"
target_name = "eqbs"
verbose = 1
pr_walnut = 0
interactive = 0
logging = False
log_file = "log.txt"
TIMEOUT= 360000

n_states = 0
memo = defaultdict()

# correct_file = "eqtm/eqtm.txt"
walnut_dir = "./" #directory where "walnut.sh" exists, ends with "/"
walnut_process = pexpect.spawn(walnut_dir+"walnut.sh", timeout=TIMEOUT)
walnut_process.expect(r"\[Walnut\]\$")

if logging:
	orig_stdout = sys.stdout
	f = open(log_file, 'w')
	sys.stdout = f

# Add continuation

# Inputs for the target automaton
input_letters = ["i", "j", "n"]
# Ensure lexicographic ordering
input_letters.sort()   
n_inputs = len(input_letters)
mem_query_info = {"count": 0, "longest": 0}
n_queries = 0

# Extra inputs for the membership automaton (if any)
extra_letters = ["t"]
member_letters = sorted(input_letters + extra_letters)
n_member = len(input_letters)

if method == "instance":
    membership_query = lambda i, j, n: f'eval memberr "?msd_{BASE} At (t<{n} => {word}[{i}+t]={word}[{j}+t])":'
elif method == "reg":
    membership_query = f'def member "?msd_{BASE} (t<n) & {word}[i+t]!={word}[j+t]":'

# Tested sequentially for counterexamples.
# It is assumed that the counterexample is the accepted string itself without any needed modifications
# e.g: If the string (i_0, j_0, n_0) is accepted, then (i_0, j_0, n_0) is the counterexample, not (i_0, j_0, n_0 - 1)
# Result automaton should be called "conj"
# Can also accept counterexamples with extra symbols at the end e.g: (i, j, n, u, v, etc.)
counterexample_tests = [
#    f'def counterr0 "?msd_{2} ($nottrib(i) | $nottrib(j) | $nottrib(n)) & ${target_name}(i,j,n)":',
    f'def counterr1 "?msd_{BASE} n=0 & ~${target_name}(i,j,n)":',
    f'def counterr2 "?msd_{BASE} u=i+n & v=j+n & ${target_name}(i,j,n+1) & {word}[u]!={word}[v]":',
    f'def counterr3 "?msd_{BASE} u=i+n & v=j+n & ${target_name}(i,j,n) & {word}[u]={word}[v] & ~${target_name}(i,j,n+1)":'
    ]
    
# For any initializations needed at the beginning. e.g: Defining a morphism
startup_commands = [
    'morphism g "0->01 1->10":',
    'promote TM g:',
    'reg fibo msd_fib "(0*|0*1)(0|01)*":',
    'reg notfib msd_2 "0*110*":',
    'reg nottrib msd_2 "0*1110*":',
    'reg tribo msd_trib "(0*11|0*1|0*) (011|01|0)*":'
    ]
if method == "reg":
    startup_commands += [membership_query]
   
membership_hash = defaultdict()
eps = ""
empty = tuple([eps for i in range(n_inputs)])
temp = ["0", "1"]
S = [empty]
E = S[:]
A = S + [tuple(map(str, a[::-1])) for a in product(temp, repeat=n_inputs)]
Tables = []

add = lambda l1, l2: tuple([x+y for x, y in zip(l1, l2)])

def run_walnut(command):
    if pr_walnut:
        print(command)
    walnut_process.sendline(command)
    walnut_process.expect(r"\[Walnut\]\$")  # Look for the expected prompt
    response = walnut_process.before.decode('utf-8').strip()
    if " at " in response:
        print(response)
        exit()
    if pr_walnut:
        print(response)
    return response
        
for command in startup_commands:
    run_walnut(command)

# Convert n to its binary k-bonacci representation.
def to_kbonacci(n, kind='fib'):
    if n < 0:
        raise ValueError("n must be non-negative")

    # 1) Build the k-bonacci sequence up to n
    if kind == 'fib':
        seq = [1, 2]            # F2=1, F3=2, ...
        max_consec = 1          # no two consecutive 1’s
        while seq[-1] + seq[-2] <= n:
            seq.append(seq[-1] + seq[-2])

    elif kind == 'trib':
        seq = [1, 2, 4]         # T2=1, T3=2, T4=4, ...
        max_consec = 2          # no three consecutive 1’s
        while seq[-1] + seq[-2] + seq[-3] <= n:
            seq.append(seq[-1] + seq[-2] + seq[-3])

    else:
        raise ValueError("kind must be 'fib' or 'trib'")

    # 2) Greedy subtraction to pick terms
    bits = []
    remaining = n
    consec = 0
    for value in reversed(seq):
        if value <= remaining and consec < max_consec:
            bits.append('1')
            remaining -= value
            consec += 1
        else:
            bits.append('0')
            consec = 0

    # 3) Strip leading zeros (represent zero as "0")
    rep = ''.join(bits).lstrip('0')
    return rep or '0'

def memoization(n, b=BASE):
    global memo
    if n in memo:
        return memo[n]
    if n <= 1:
        return n
    if b == "fib":
        memo[n] = memoization(n - 1) + memoization(n - 2)
        return memo[n]
    if b == "trib":
        if n == 2:
            return 1
        memo[n] = memoization(n - 1) + memoization(n - 2) + memoization(n - 3)
        return memo[n]  
    
def valid_rep(st, b=BASE):
    if b == "fib":
        run_walnut(f'reg num msd_{BASE} "{st}":')
        return run_walnut(f'eval reptest "?msd_{BASE} Ex $num(x) & $fibo(x)":')[-4:] == "TRUE"
    elif b == "trib":
        run_walnut(f'reg num msd_{BASE} "{st}":')
        return run_walnut(f'eval reptest "?msd_{BASE} Ex $num(x) & $tribo(x)":')[-4:] == "TRUE"    
    else:
        return True

def to_decimal(tup_strings, b=BASE):
    if b == "fib" or b == "trib":
        converted = list()
        for s in tup_strings:
            if valid_rep(s):
                temp = 0
                for i in range(1, len(s)+1):
                    if s[-i] == "0":
                        continue
                    n = (i - 1) + 2
                    temp += memoization(n, b)
            else:
                temp = -1
            converted.append(temp)
        return converted

    else:
        return [int(s, 2) for s in tup_strings]

def is_member(string):
    t0 = time()
    global membership_time
    global membership_hash
    global mem_query_info
    global n_queries
    n_queries += 1
    mem_query_info["count"] += 1
    mem_query_info["longest"] = max(mem_query_info["longest"], len(string[0]))
    try:
        return membership_hash[string]
    except:
        for one in string:
            if not valid_rep(one):
                membership_hash[string] = False
                return False
        if method == "instance":
            params = to_decimal(string)
            if -1 in params:
                print("HUGE ERROR:\n", params)
                input()
            command = membership_query(*params)
            response = run_walnut(command)
            res = response[-5:] != "FALSE"
        elif method == "reg":
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
    global n_states
    n_states = len(trans_func.keys())
    walnut_automaton = f"msd_{BASE} " * n_inputs + "\n"
    for i in range(len(Qs)):
        walnut_automaton += f"\n{i} {int(i in F)}\n"
        for j in range(1, len(A)):
            a = A[j]
            line = f"{' '.join(a)} -> {trans_func[i][a]}\n"
            walnut_automaton += line
            
    return walnut_automaton

def BFS(trans_func, F):
    start = 0
    if start in F:
        return []
    queue = deque()
    queue.append((start, []))
    visited = set()
    visited.add(start)
    while queue:
        current_state, path = queue.popleft()
        transitions = trans_func.get(current_state, {})
        for triplet in transitions:
            next_state = transitions[triplet]
            if next_state in F:
                return path + [triplet]
            if next_state not in visited:
                visited.add(next_state)
                queue.append((next_state, path + [triplet]))
    return None


def pad_binaries(bin_tuple):
    max_len = 0
    for bin_i in bin_tuple:
        max_len = max(max_len, len(bin_i))
    return tuple([bin_i.zfill(max_len) for bin_i in bin_tuple])

def no_leading_zero(t):
    min_cut = next((i for i, chars in enumerate(zip(*t)) if any(c != '0' for c in chars)), len(t[0]))
    return tuple(s[min_cut:] for s in t)

def check_tests(conj):
    automata_dir = walnut_dir + f"Automata Library/{target_name}.txt"
    with open(automata_dir, "w") as conj_file:
        conj_file.write(conj)
    for t in range(len(counterexample_tests)):
        test = counterexample_tests[t]
        run_walnut(test)
        name = test.split()[1]
        
        """
        result = run_walnut(f"test {name} 1:")
        if result[-1] == ']':
            print(f'Failed "test {t}",', end=" ")
            text = result.split('\n')[-1]
            segments = text.strip('[]').split('][')
            arrays = [segment.split(', ') for segment in segments]
            counter_ex = tuple(["".join(arrays[j][i] for j in range(len(arrays))) for i in range(n_inputs)])
            return False, counter_ex
        """
        
        test_automaton = walnut_dir + f"Automata Library/{name}.txt"
        with open(test_automaton, "r") as ta:
            trans_ff, ff = parse_automaton(ta.read())        
        result = BFS(trans_ff, ff)
        if result:
            print(f'Failed "test {t}"', end=" ")
            print(result)
            counter_ex = tuple(["".join(result[j][i] for j in range(len(result))) for i in range(n_inputs)])
            counter_ex = no_leading_zero(counter_ex)
            #print(counter_ex)
            if name != "counterr0":
                #print(counter_ex)
                if run_automaton(conj, counter_ex) == is_member(counter_ex):
                    if BASE == "fib" or BASE == "trib":
                        n_new = to_kbonacci(to_decimal([counter_ex[2]], BASE)[0] + 1, BASE)
                    elif BASE == "2":
                        n_new = bin(to_decimal([counter_ex[2]], BASE)[0] + 1)[2:]
                    else:
                        print("ERROR: New base used")
                        exit()
                    counter_ex = no_leading_zero(pad_binaries((counter_ex[0], counter_ex[1], n_new)))
                    print("MODIFIED")
            return False, counter_ex
        
    return True, 0




def test_conj(conj):
    res = check_tests(conj)
    if res[0]:
        return True, None
    return False, res[1]

def parse_automaton(data):
    lines = data.strip().split("\n")
    num_inputs = lines[0].count("msd_{BASE}")  # Number of input bits

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

print(f'\nExperiment Parameters: base = {BASE}, word = "{word}", method = "{method}", automaton name = {target_name}')
print("Walnut Counterexample Tests:")
for i in range(len(counterexample_tests)):
	print(f"test {i}:	{counterexample_tests[i]}")
	
while True:
    if interactive:
        print("\nPress Enter for next iteration.")
        input()
    iteration += 1
    print("\n" + "-"*30 + "\n")
    print("Iteration:", iteration)
    print(f"n_rows = {len(Tables[-1].keys())}, |S| = {len(S)}, |E| = {len(E)}")
    if verbose:
        print_table()
        print("S =", S)
        print("E =", E)
    print("\nChecking consistency...", end=" ")
    mem_query_info = {"count": 0, "longest": 0}
    res = is_consistent()
    print(f"Done.\n{mem_query_info['count']} new membership queries", end="")
    if mem_query_info['count']:
    	print(f", longest of length {mem_query_info['longest']}.")
    else:
    	print()
    if not res[0]:
        k, l, i, j = res[1]
        ae = add(A[k], E[l])
        E.append(ae)
        print("Table is NOT consistent!\nExtending set E...", end=" ")
        extend_E()
        print("Done.")
        if verbose:            
            print(f"s1 = {S[i]}, s2 = {S[j]}, a = {A[k]}, e = {E[l]}")
        continue
    print("Table is consistent.\n") 

    print("Checking closed property...", end=" ")
    res = is_closed()
    print("Done.")
    if not res[0]:
        i, j = res[1]
        sa = add(S[i], A[j])
        S.append(sa)
        print("Table is NOT closed!\nExtending set S...", end=" ")
        extend_S(1)
        print("Done.")
        if verbose:
            print(f"s = {S[i]}, a = {A[j]}")
        continue
    print("Table is closed.")
    
    print("\nPassed both consistency and closed tests. Forming hypothesis...")
    conj = make_conj()
    print(f"Hypothesis has {n_states} states. Checking hypothesis...")
    if verbose:
        print(conj)
    res = test_conj(conj)
    print(f"Hypothesis is {res[0]}\n")
    if not res[0]:
        t = res[1]
        if verbose:
            print("Counterexample string:", t)
        print(f"Smallest counterexample has length {len(t[0])}\nAdding prefixes to set S...", end=" ")
        mem_query_info = {"count": 0, "longest": 0}
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
        print(f"Done\n{mem_query_info['count']} new membership queries, longest of length {mem_query_info['longest']}.")
    else:
        print("-"*30 + "\n")
        print("DONE !!!\n")
        break
        
walnut_process.terminate()
time1 = time()

'''
def secondsToStr(t):
    return "%d:%02d:%02d.%03d" % \
        reduce(lambda ll,b : divmod(ll[0],b) + ll[1:],
            [(t*1000,),1000,60,60])
'''

print("Statistics:")
print("total time =", time1-time0, "seconds")
print("time taken by membership queries =", membership_time, "seconds")
print("total number of membership queries =", n_queries, "queries")
print("total number of unique queries =", len(membership_hash.items()), "queries")
if (BASE == "fib" or BASE == "trib") and method == "instance":
	print(f"largest n calculated for {BASE} is", max(memo))

if logging:
	sys.stdout = orig_stdout
	f.close()
