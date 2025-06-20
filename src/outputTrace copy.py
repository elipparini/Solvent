
from z3 import *
import time
import sys


def stringOfXA(m, i):
    return "A" + str(m.eval(xa[i]))


def stringOfTx(m, i):
    contract = "C4"
    sender = stringOfXA(m, i)
    method = str(m.eval(f[i]))
    args = str(m.eval(xn[i]))
    return "-- " + sender + ": " + contract + "." + method + "(" + args + ") -->"


def stringOfWal(m, i):
    s = ""
    for j in range(A+1):
        s += "A" + str(j) + "[" + str(m.eval(aw[i][j])) + ":T] | "
    return s


def stringOfContr(m, i):
    contract = "C4"
    return contract + "[" + str(m.eval(w[i])) + ":T] "


def stringOfSuccess(m, i):
    s = "| success:"
    return s + str(m.eval(success[i]))


def printState(m):
    for i in range(N):
        print(stringOfWal(m, i), end='')
        print(stringOfContr(m, i), end='')
        print(stringOfSuccess(m, i), end='')
        print()
        print(stringOfTx(m, i), end='')
        print()
    print(stringOfWal(m, N), end='')
    print(stringOfContr(m, N), end='')
    print()


timeStart = time.time()

# N = upper bound on the length of trace
N = 10

# A = upper bound on the number of actors (A+1)
A = 2

# Maximum functions depth
M = 50

# Contract's balance
w = [Int("w_%s" % (i)) for i in range(N+1)]
w_q0 = Int("wq0")
w_q1 = Int("wq1")


# Block number
block_num = [Int("block_num_%s" % (i)) for i in range(N+1)]
err = [Bool("err_%s" % (i)) for i in range(N+1)]
err_q0 = Bool("err_q0")
err_q1 = Bool("err_q1")


Proc = Datatype('Proc')
Proc.declare('pay_func')
Proc.declare('coinbase')

Proc = Proc.create()

# Contract's state variables

owner = [Int("owner_%s" % (i)) for i in range(N+1)]
t_owner = [[Int("t_owner_%s_%s" % (i, m)) for m in range(M)] for i in range(N+1)]
owner_q0 = Int("ownerq0")
t_owner_q0 = [Int("t_ownerq0_%s" % (m)) for m in range(M)]
owner_q1 = Int("ownerq1")
t_owner_q1 = [Int("t_ownerq1_%s" % (m)) for m in range(M)]
maxCount = [Int("maxCount_%s" % (i)) for i in range(N+1)]
t_maxCount = [[Int("t_maxCount_%s_%s" % (i, m)) for m in range(M)] for i in range(N+1)]
maxCount_q0 = Int("maxCountq0")
t_maxCount_q0 = [Int("t_maxCountq0_%s" % (m)) for m in range(M)]
maxCount_q1 = Int("maxCountq1")
t_maxCount_q1 = [Int("t_maxCountq1_%s" % (m)) for m in range(M)]
count = [Int("count_%s" % (i)) for i in range(N+1)]
t_count = [[Int("t_count_%s_%s" % (i, m)) for m in range(M)] for i in range(N+1)]
count_q0 = Int("countq0")
t_count_q0 = [Int("t_countq0_%s" % (m)) for m in range(M)]
count_q1 = Int("countq1")
t_count_q1 = [Int("t_countq1_%s" % (m)) for m in range(M)]

# Called procedure
f = [Const("f_%s" % (i), Proc) for i in range(N+1)]
f_q0 = Const("f_q0", Proc)
f_q1 = Const("f_q1", Proc)


# users' wallets
aw = [[Int("aw_%s_%s" % (i, j)) for j in range(A+1)] for i in range(N+1)]
aw_q0 = [Int("awq0_%s" % j) for j in range(A+1)]
aw_q1 = [Int("awq1_%s" % j) for j in range(A+1)]


# msg.sender
xa = [Int("xa_%s" % (i)) for i in range(N+1)]
xa_q = Int("xa_q")

# msg.value
xn = [Int("xn_%s" % (i)) for i in range(N+1)]
xn_q0 = Int("xn_q0")
xn_q1 = Int("xn_q1")


# functions args


# List of ids hard coded
hard_coded_list = [0]

# Temporary contract balance. Used inside functions to model internal states
t_w = [[Int("t_w_%s_%s" % (i, m)) for m in range(M)] for i in range(N+1)]
t_w_q0 = [Int("t_wq0_%s" % (m)) for m in range(M)]
t_w_q1 = [Int("t_wq1_%s" % (m)) for m in range(M)]
 

# Temporary users wallets
t_aw = [[[Int("t_aw_%s_%s_%s" % (i, m, j)) for j in range(A+1)]
         for m in range(M)] for i in range(N+1)]

t_aw_q0 = [[Int("t_awq0_%s_%s" % (m, j)) for j in range(A+1)] for m in range(M)]
t_aw_q1 = [[Int("t_awq1_%s_%s" % (m, j)) for j in range(A+1)] for m in range(M)]


s = Solver()

def next_state_tx(aw1, aw2, w1, w2, ownerNow, ownerNext, maxCountNow, maxCountNext, countNow, countNext):
    return And(w2 == w1,
               And([aw2[j] == aw1[j] for j in range(A+1)])
               , ownerNow==ownerNext, maxCountNow==maxCountNext, countNow==countNext
               )

def send(sender_id, amount, w_b, w_a, aw_b, aw_a): # '_b' and '_a' mean 'before' and 'after'
    return And(w_a == w_b - amount,
                  And([If(j == sender_id,
                          aw_a[j] == aw_b[j] + amount,
                          aw_a[j] == aw_b[j]) for j in range(A+1)]))

def receive(sender_id, amount, w_b, w_a, aw_b, aw_a):
        return And(w_a == w_b + amount,
                  And([If(j == sender_id,
                          aw_a[j] == aw_b[j] - amount,
                          aw_a[j] == aw_b[j]) for j in range(A+1)])) 


def constructor(xa1, xn1, awNow, awNext, wNow, wNext, t_aw, t_w, block_num, ownerNow, ownerNext, t_owner, maxCountNow, maxCountNext, t_maxCount, countNow, countNext, t_count, err):
    return And(receive(xa1, xn1, wNow, t_w[0], awNow, t_aw[0]), 
	And(
        And(
	xn1>0,
	And(
	t_owner[0] == xa1,
	And(
	t_maxCount[0] == 3,
	t_count[0] == 0))), 
        err == Or(False, Not(And([Or(j != xa1, xn1 <= awNow[j]) for j in range(A+1)]))), 
        True, 
        t_owner[0]>=1, t_owner[0]<=A, 
        Or(
            And(err==True, next_state_tx(awNow, awNext, wNow, wNext, ownerNow, ownerNext, maxCountNow, maxCountNext, countNow, countNext)), 
            And(err==False, next_state_tx(t_aw[0], awNext, t_w[0], wNext, t_owner[0], ownerNext, t_maxCount[0], maxCountNext, t_count[0], countNext)))))

def pay_func(xa1, xn1, awNow, awNext, wNow, wNext, t_aw, t_w, block_num, ownerNow, ownerNext, t_owner, maxCountNow, maxCountNext, t_maxCount, countNow, countNext, t_count, err):
    return And(True, 
	And(And(
	True,
	If(And(xa1 == ownerNow),And(t_count[0] == (countNow+1), True, wNow==t_w[0], And([awNow[j] == t_aw[0][j] for j in range(A+1)])),And(And(
	t_count[0] == countNow,
	send(xa1, wNow, wNow, t_w[0], awNow, t_aw[0])), True))), err == Or(False, Not(xn1==0), Not(countNow<maxCountNow), Not(wNow>= 0)), True, ownerNow==ownerNext, maxCountNow==maxCountNext, Or(And(err==True, next_state_tx(awNow, awNext, wNow, wNext, ownerNow, ownerNext, maxCountNow, maxCountNext, countNow, countNext)), And(err==False, next_state_tx(t_aw[0], awNext, t_w[0], wNext, ownerNow, ownerNext, maxCountNow, maxCountNext, t_count[0], countNext)))))

def coinbase(xa1, xn1, awNow, awNext, wNow, wNext, t_aw, t_w, block_num, ownerNow, ownerNext, t_owner, maxCountNow, maxCountNext, t_maxCount, countNow, countNext, t_count, err):
	return And(err == False, t_w[0] == wNow + xn1, next_state_tx(awNow, awNext, t_w[0], wNext, ownerNow, ownerNext, maxCountNow, maxCountNext, countNow, countNext))


def user_is_legit(xa1):
    return And(xa1 >= 1, xa1 <= A)


def user_has_not_already_played(xa, xa1, f, i):
    return Not(Or([And(xa[k] == xa1, f[k] == Proc.pay) for k in range(i)]))


def user_is_not_hard_coded(xa1):
    return Not(Or([xa1 == hc_i for hc_i in hard_coded_list]))


def user_is_fresh(xa, xa1, f, i):
    return And(user_is_not_hard_coded(xa1), user_has_not_already_played(xa, xa1, f, i))

# transition rules

def step_trans(f1, xa1, xn1,  aw1, aw2, w1, w2, t_aw, t_w, block_num1, block_num2, i, ownerNow, ownerNext, t_owner, maxCountNow, maxCountNext, t_maxCount, countNow, countNext, t_count, err):
    return And(And(xn1 >= 0, w2 >= 0),
               And([aw1[j] >= 0 for j in range(A+1)]),
               block_num2 >= block_num1,
               ownerNext >= 0, ownerNext <= A, 
               	If(f1 == Proc.coinbase, And(xa1 == 0, 
	coinbase(xa1, xn1, aw1, aw2, w1, w2, t_aw, t_w, block_num1, ownerNow, ownerNext, t_owner, maxCountNow, maxCountNext, t_maxCount, countNow, countNext, t_count, err)),
And(xa1 >= 1, xa1 <= A, 		pay_func(xa1, xn1, aw1, aw2, w1, w2, t_aw, t_w, block_num1, ownerNow, ownerNext, t_owner, maxCountNow, maxCountNext, t_maxCount, countNow, countNext, t_count, err))))

# initial state
s.add(w[0] >= 0)
               
new_state = And(And(xa[0] >= 0, xa[0] <= A, xn[0] >= 0),
               And([aw[0][j] >= 0 for j in range(A+1)]),
                  constructor(xa[0], xn[0],  aw[0], aw[1], w[0], w[1], t_aw[0], t_w[0], block_num[0], owner[0], owner[1], t_owner[0], maxCount[0], maxCount[1], t_maxCount[0], count[0], count[1], t_count[0], err[1]))
s.add(new_state)
for i in range(1, N):
    new_state = step_trans(f[i], xa[i], xn[i],  aw[i],
                           aw[i+1], w[i], w[i+1], t_aw[i], t_w[i], block_num[i], block_num[i+1], i, owner[i], owner[i+1], t_owner[i], maxCount[i], maxCount[i+1], t_maxCount[i], count[i], count[i+1], t_count[i], err[i+1])
    s.add(new_state)


# print(s)

# def p(i):
#     t_awq_list = [t_awq_m_j for t_awq_m in t_aw_q for t_awq_m_j in t_awq_m]
#     #print([xn_q, f_q, w_q, *aw_q, *t_w_q, *t_awq_list ])
#     return And(w[i] > 0,
#                Exists([xa_q], And(user_is_legit(xa_q), user_is_fresh(xa, xa_q, f,  i),
#                       ForAll([xn_q, f_q, w_q, *aw_q, *t_w_q, *t_awq_list, owner_q, *t_owner_q, maxCount_q, *t_maxCount_q, count_q, *t_count_q ], Or(Not(step_trans(f_q, xa_q, xn_q, aw[i], aw_q, w[i], w_q, t_aw_q, t_w_q, i, owner[i], owner_q, t_owner_q, maxCount[i], maxCount_q, t_maxCount_q, count[i], count_q, t_count_q)), w_q > 0)))))
#                       #ForAll([xn_q, f_q, w_q, *aw_q ], Or(Not(step_trans(f_q, xa_q, xn_q, aw[i], aw_q, w[i], w_q, t_aw[i], t_w[i], i)), w_q > 0)))))



def p_liquidity1_liquid_1(i):
    t_awq_list0 = [t_awq_m_j for t_awq_m in t_aw_q0 for t_awq_m_j in t_awq_m]; 
    return And(
        Exists([xa_q], And(user_is_legit(xa_q), And(And(And(w[i]>0,count[i]<maxCount[i]),owner[i]!=xa_q),1 == owner[i]),
            ForAll([xn_q0, f_q0, w_q0, *aw_q0, *t_w_q0, *t_awq_list0, err_q0, owner_q0, *t_owner_q0, maxCount_q0, *t_maxCount_q0, count_q0, *t_count_q0],  
                Or(
Not(step_trans(f_q0, xa_q, xn_q0, aw[i], aw_q0, w[i], w_q0, t_aw_q0, t_w_q0, block_num[i], block_num[i], i+0, owner[i], owner_q0, t_owner_q0, maxCount[i], maxCount_q0, t_maxCount_q0, count[i], count_q0, t_count_q0, err_q0)),

Not(And([Or(j != xa_q, aw_q0[j] == (aw[i][j]+w[i])) for j in range(A+1)]))
        )))))

def p_liquidity2_notliquid_1(i):
    t_awq_list0 = [t_awq_m_j for t_awq_m in t_aw_q0 for t_awq_m_j in t_awq_m]; 
    return And(
        Exists([xa_q], And(user_is_legit(xa_q), And(w[i]>0,count[i]<maxCount[i]),
            ForAll([xn_q0, f_q0, w_q0, *aw_q0, *t_w_q0, *t_awq_list0, err_q0, owner_q0, *t_owner_q0, maxCount_q0, *t_maxCount_q0, count_q0, *t_count_q0],  
                Or(
Not(step_trans(f_q0, xa_q, xn_q0, aw[i], aw_q0, w[i], w_q0, t_aw_q0, t_w_q0, block_num[i], block_num[i], i+0, owner[i], owner_q0, t_owner_q0, maxCount[i], maxCount_q0, t_maxCount_q0, count[i], count_q0, t_count_q0, err_q0)),

Not(And([Or(j != xa_q, aw_q0[j] == (aw[i][j]+w[i])) for j in range(A+1)]))
        )))))
def p_liquidity2_notliquid_2(i):
    t_awq_list0 = [t_awq_m_j for t_awq_m in t_aw_q0 for t_awq_m_j in t_awq_m]; t_awq_list1 = [t_awq_m_j for t_awq_m in t_aw_q1 for t_awq_m_j in t_awq_m]; 
    return And(
        Exists([xa_q], And(user_is_legit(xa_q), And(w[i]>0,count[i]<maxCount[i]),
            ForAll([xn_q0, f_q0, w_q0, *aw_q0, *t_w_q0, *t_awq_list0, err_q0, owner_q0, *t_owner_q0, maxCount_q0, *t_maxCount_q0, count_q0, *t_count_q0, xn_q1, f_q1, w_q1, *aw_q1, *t_w_q1, *t_awq_list1, err_q1, owner_q1, *t_owner_q1, maxCount_q1, *t_maxCount_q1, count_q1, *t_count_q1],  
                Or(
Not(step_trans(f_q0, xa_q, xn_q0, aw[i], aw_q0, w[i], w_q0, t_aw_q0, t_w_q0, block_num[i], block_num[i], i+0, owner[i], owner_q0, t_owner_q0, maxCount[i], maxCount_q0, t_maxCount_q0, count[i], count_q0, t_count_q0, err_q0)),
Not(step_trans(f_q1, xa_q, xn_q1, aw_q0, aw_q1, w_q0, w_q1, t_aw_q1, t_w_q1, block_num[i], block_num[i], i+1, owner_q0, owner_q1, t_owner_q1, maxCount_q0, maxCount_q1, t_maxCount_q1, count_q0, count_q1, t_count_q1, err_q1)),

Not(And([Or(j != xa_q, aw_q1[j] == (aw[i][j]+w[i])) for j in range(A+1)]))
        )))))

def p_liquidity3_notliquid_1(i):
    t_awq_list0 = [t_awq_m_j for t_awq_m in t_aw_q0 for t_awq_m_j in t_awq_m]; 
    return And(
        Exists([xa_q], And(user_is_legit(xa_q), And(w[i]>0,owner[i]!=xa_q),
            ForAll([xn_q0, f_q0, w_q0, *aw_q0, *t_w_q0, *t_awq_list0, err_q0, owner_q0, *t_owner_q0, maxCount_q0, *t_maxCount_q0, count_q0, *t_count_q0],  
                Or(
Not(step_trans(f_q0, xa_q, xn_q0, aw[i], aw_q0, w[i], w_q0, t_aw_q0, t_w_q0, block_num[i], block_num[i], i+0, owner[i], owner_q0, t_owner_q0, maxCount[i], maxCount_q0, t_maxCount_q0, count[i], count_q0, t_count_q0, err_q0)),

Not(And([Or(j != xa_q, aw_q0[j] == (aw[i][j]+w[i])) for j in range(A+1)]))
        )))))
def p_liquidity3_notliquid_2(i):
    t_awq_list0 = [t_awq_m_j for t_awq_m in t_aw_q0 for t_awq_m_j in t_awq_m]; t_awq_list1 = [t_awq_m_j for t_awq_m in t_aw_q1 for t_awq_m_j in t_awq_m]; 
    return And(
        Exists([xa_q], And(user_is_legit(xa_q), And(w[i]>0,owner[i]!=xa_q),
            ForAll([xn_q0, f_q0, w_q0, *aw_q0, *t_w_q0, *t_awq_list0, err_q0, owner_q0, *t_owner_q0, maxCount_q0, *t_maxCount_q0, count_q0, *t_count_q0, xn_q1, f_q1, w_q1, *aw_q1, *t_w_q1, *t_awq_list1, err_q1, owner_q1, *t_owner_q1, maxCount_q1, *t_maxCount_q1, count_q1, *t_count_q1],  
                Or(
Not(step_trans(f_q0, xa_q, xn_q0, aw[i], aw_q0, w[i], w_q0, t_aw_q0, t_w_q0, block_num[i], block_num[i], i+0, owner[i], owner_q0, t_owner_q0, maxCount[i], maxCount_q0, t_maxCount_q0, count[i], count_q0, t_count_q0, err_q0)),
Not(step_trans(f_q1, xa_q, xn_q1, aw_q0, aw_q1, w_q0, w_q1, t_aw_q1, t_w_q1, block_num[i], block_num[i], i+1, owner_q0, owner_q1, t_owner_q1, maxCount_q0, maxCount_q1, t_maxCount_q1, count_q0, count_q1, t_count_q1, err_q1)),

Not(And([Or(j != xa_q, aw_q1[j] == (aw[i][j]+w[i])) for j in range(A+1)]))
        )))))



queries = {}
queries['liquidity2_notliquid'] = [[p_liquidity2_notliquid_1(i),p_liquidity2_notliquid_2(i)] for i in range(1, N+1)]
queries['liquidity3_notliquid'] = [[p_liquidity3_notliquid_1(i),p_liquidity3_notliquid_2(i)] for i in range(1, N+1)]
queries['liquidity1_liquid'] = [[p_liquidity1_liquid_1(i)] for i in range(1, N+1)]


for prop in {'liquidity2_notliquid','liquidity3_notliquid','liquidity1_liquid'}:
    for i, q in enumerate(queries[prop]):
        for j in range(0, len(q)):
            
            qj = q[j]
            s2 = Solver()
            s2.add(s.assertions())
            s2.add(qj)
            text = s2.to_smt2()
            # text = '(set-logic ALL)\n' + text
            text = '(set-logic ALL)\n' + text + '\n(get-model)' 
            filename = 'out/smt2/%s/tracebased/%s/output_%s.smt2'%(prop, str(i).zfill(len(str(len(queries[prop])))), str(j).zfill(len(str(len(q)))))
            if not os.path.exists('out/smt2/'):
                os.makedirs('out/smt2/')
            if not os.path.exists('out/smt2/%s/'%(prop)):
                os.makedirs('out/smt2/%s/'%(prop))
            if not os.path.exists('out/smt2/%s/tracebased/'%(prop)):
                os.makedirs('out/smt2/%s/tracebased/'%(prop))
            if not os.path.exists('out/smt2/%s/tracebased/%s/'%(prop, str(i).zfill(len(str(len(queries[prop])))))):
                os.makedirs('out/smt2/%s/tracebased/%s/'%(prop, str(i).zfill(len(str(len(queries[prop]))))))
            with open(filename, 'w') as my_file:
                my_file.write(text)

# timeStart = time.time()
# for prop in {'liquidity2_notliquid','liquidity3_notliquid','liquidity1_liquid'}:
#     print('Property [' + prop + ']')
#     for i, q in enumerate(queries[prop]):
#         liquid = False
#         for j in range(0, len(q)):
#             qj = q[j] 
#             resj = s.check(qj)
#             if resj == unsat:
#                 liquid = True
#                 break
#         if not liquid:
#             break
#     if not liquid: print("not liquid [in 2 steps]")
#     else: print("liquid [in 2 steps]")
#     timeTot = time.time() - timeStart
#     print("Solving time: " + str(timeTot) + "s")
               
