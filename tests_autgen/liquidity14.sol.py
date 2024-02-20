
from z3 import *
import time


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
N = 2

# A = upper bound on the number of actors (A+1)
A = 1

# Maximum functions depth
M = 1

# Contract's balance
w = [Int("w_%s" % (i)) for i in range(N+1)]
w_q0 = Int("wq0")
w_q1 = Int("wq1")


# Block number
block_num = [Int("block_num_%s" % (i)) for i in range(N+1)]
block_num_q0 = Int("block_num_q0")
block_num_q1 = Int("block_num_q1")


Proc = Datatype('Proc')
Proc.declare('unlock')
Proc.declare('pay')

Proc = Proc.create()

# Contract's state variables

b = [Bool("b_%s" % (i)) for i in range(N+1)]
t_b = [[Bool("t_b_%s_%s" % (i, m)) for m in range(M)] for i in range(N+1)]
b_q0 = Bool("bq0")
t_b_q0 = [Bool("t_bq0_%s" % (m)) for m in range(M)]
b_q1 = Bool("bq1")
t_b_q1 = [Bool("t_bq1_%s" % (m)) for m in range(M)]

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
pay_amount = [Int("pay_amount_%s" % (i)) for i in range(N+1)]
pay_amount_q0 = Int("pay_amount0_q")
pay_amount_q1 = Int("pay_amount1_q")

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

# initial state
s.add(w[0] >= 0)
# s.add(w[0] == 1)

def next_state_tx(aw1, aw2, w1, w2, bNow, bNext):
    return And(w2 == w1,
               And([aw2[j] == aw1[j] for j in range(A+1)])
               , bNow==bNext
               , )

def send(sender_id, amount, w_b, w_a, aw_b, aw_a): # '_b' and '_a' mean 'before' and 'after'
    return And(w_a == w_b - amount,
                  And([If(j == sender_id,
                          aw_a[j] == aw_b[j] + amount,
                          aw_a[j] == aw_b[j]) for j in range(A+1)]))


def constructor(xa1, xn1, awNow, awNext, wNow, wNext, t_aw, t_w, block_num, bNow, bNext, t_b):
    return If(Not(xn1==0), next_state_tx(awNow, awNext, wNow, wNext, bNow, bNext), 
	And(And(
	t_b[0] == False,
	next_state_tx(awNow, awNext, wNow, wNext, t_b[0], bNext)), next_state_tx(awNow, awNext, wNow, wNext, t_b[0], bNext)))

def unlock(xa1, xn1, awNow, awNext, wNow, wNext, t_aw, t_w, block_num, bNow, bNext, t_b):
    return If(Not(xn1==0), next_state_tx(awNow, awNext, wNow, wNext, bNow, bNext), 
	And(If(
	Not(Not(bNow)), 
		next_state_tx(awNow, awNext, wNow, wNext, bNow, bNext), And(
		And(t_b[0] == True,next_state_tx(awNow, awNext, wNow, wNext, t_b[0], bNext))))))

def pay(xa1, xn1, pay_amount, awNow, awNext, wNow, wNext, t_aw, t_w, block_num, bNow, bNext, t_b):
    return If(Not(xn1==0), next_state_tx(awNow, awNext, wNow, wNext, bNow, bNext), 
	And(If(
	Not(And(pay_amount<=wNow,bNow)), 
		next_state_tx(awNow, awNext, wNow, wNext, bNow, bNext), And(
		And(And(
	t_b[0] == False,
	If(
	Not(pay_amount >= 0), 
		next_state_tx(awNow, awNext, wNow, wNext, bNow, bNext), And(send(xa1, pay_amount, wNow, t_w[0], awNow, t_aw[0]), next_state_tx(t_aw[0], awNext, t_w[0], wNext, t_b[0], bNext)))),next_state_tx(t_aw[0], awNext, t_w[0], wNext, t_b[0], bNext))))))


def user_is_legit(xa1):
    return And(xa1 >= 0, xa1 <= A)


def user_has_not_already_played(xa, xa1, f, i):
    return Not(Or([And(xa[k] == xa1, f[k] == Proc.pay) for k in range(i)]))


def user_is_not_hard_coded(xa1):
    return Not(Or([xa1 == hc_i for hc_i in hard_coded_list]))


def user_is_fresh(xa, xa1, f, i):
    return And(user_is_not_hard_coded(xa1), user_has_not_already_played(xa, xa1, f, i))

# transition rules

def step_trans(f1, xa1, xn1, pay_amount, aw1, aw2, w1, w2, t_aw, t_w, block_num1, block_num2, i, bNow, bNext, t_b):
    return And(And(xa1 >= 0, xa1 <= A, xn1 >= 0),
               And([aw1[j] >= 0 for j in range(A+1)]),
               block_num2 >= block_num1,
               If(f1 == Proc.unlock,
	unlock(xa1, xn1, aw1, aw2, w1, w2, t_aw, t_w, block_num1, bNow, bNext, t_b),
		pay(xa1, xn1, pay_amount, aw1, aw2, w1, w2, t_aw, t_w, block_num1, bNow, bNext, t_b)))

new_state = And(And(xa[0] >= 0, xa[0] <= A, xn[0] >= 0),
               And([aw[0][j] >= 0 for j in range(A+1)]),
                  constructor(xa[0], xn[0],  aw[0], aw[1], w[0], w[1], t_aw[0], t_w[0], block_num[0], b[0], b[1], t_b[0]))
s.add(new_state)
for i in range(1, N):
    new_state = step_trans(f[i], xa[i], xn[i], pay_amount[i], aw[i],
                           aw[i+1], w[i], w[i+1], t_aw[i], t_w[i], block_num[i], block_num[i+1], i, b[i], b[i+1], t_b[i])
    s.add(new_state)


# print(s)

# def p(i):
#     t_awq_list = [t_awq_m_j for t_awq_m in t_aw_q for t_awq_m_j in t_awq_m]
#     #print([xn_q, f_q, w_q, *aw_q, *t_w_q, *t_awq_list ])
#     return And(w[i] > 0,
#                Exists([xa_q], And(user_is_legit(xa_q), user_is_fresh(xa, xa_q, f,  i),
#                       ForAll([xn_q, f_q, w_q, *aw_q, *t_w_q, *t_awq_list, pay_amount_q, b_q, *t_b_q ], Or(Not(step_trans(f_q, xa_q, xn_q, pay_amount_q, aw[i], aw_q, w[i], w_q, t_aw_q, t_w_q, i, b[i], b_q, t_b_q)), w_q > 0)))))
#                       #ForAll([xn_q, f_q, w_q, *aw_q ], Or(Not(step_trans(f_q, xa_q, xn_q, aw[i], aw_q, w[i], w_q, t_aw[i], t_w[i], i)), w_q > 0)))))


def p_liquidity14c_liq_1(i):
    t_awq_list0 = [t_awq_m_j for t_awq_m in t_aw_q0 for t_awq_m_j in t_awq_m]; 
    return And(
        Exists([xa_q], And(user_is_legit(xa_q), True,
            ForAll([xn_q0, f_q0, w_q0, *aw_q0, *t_w_q0, *t_awq_list0, block_num_q0, pay_amount_q0, b_q0, *t_b_q0],  
                Or(
Not(step_trans(f_q0, xa_q, xn_q0, pay_amount_q0, aw[i], aw_q0, w[i], w_q0, t_aw_q0, t_w_q0, block_num[i], block_num_q0, i+0, b[i], b_q0, t_b_q0)),

And([Or(j != xa_q, Not(aw_q0[j] == aw[i][j]+w[i])) for j in range(A+1)])
        )))))
def p_liquidity14c_liq_2(i):
    t_awq_list0 = [t_awq_m_j for t_awq_m in t_aw_q0 for t_awq_m_j in t_awq_m]; t_awq_list1 = [t_awq_m_j for t_awq_m in t_aw_q1 for t_awq_m_j in t_awq_m]; 
    return And(
        Exists([xa_q], And(user_is_legit(xa_q), True,
            ForAll([xn_q0, f_q0, w_q0, *aw_q0, *t_w_q0, *t_awq_list0, block_num_q0, pay_amount_q0, b_q0, *t_b_q0, xn_q1, f_q1, w_q1, *aw_q1, *t_w_q1, *t_awq_list1, block_num_q1, pay_amount_q1, b_q1, *t_b_q1],  
                Or(
Not(step_trans(f_q0, xa_q, xn_q0, pay_amount_q0, aw[i], aw_q0, w[i], w_q0, t_aw_q0, t_w_q0, block_num[i], block_num_q0, i+0, b[i], b_q0, t_b_q0)),
Not(step_trans(f_q1, xa_q, xn_q1, pay_amount_q1, aw_q0, aw_q1, w_q0, w_q1, t_aw_q1, t_w_q1, block_num_q0, block_num_q1, i+1, b_q0, b_q1, t_b_q1)),

And([Or(j != xa_q, Not(aw_q1[j] == aw[i][j]+w[i])) for j in range(A+1)])
        )))))

def p_liquidity14d_liq_1(i):
    t_awq_list0 = [t_awq_m_j for t_awq_m in t_aw_q0 for t_awq_m_j in t_awq_m]; 
    return And(
        Exists([xa_q], And(user_is_legit(xa_q), b[i]==True,
            ForAll([xn_q0, f_q0, w_q0, *aw_q0, *t_w_q0, *t_awq_list0, block_num_q0, pay_amount_q0, b_q0, *t_b_q0],  
                Or(
Not(step_trans(f_q0, xa_q, xn_q0, pay_amount_q0, aw[i], aw_q0, w[i], w_q0, t_aw_q0, t_w_q0, block_num[i], block_num_q0, i+0, b[i], b_q0, t_b_q0)),

And([Or(j != xa_q, Not(aw_q0[j] == aw[i][j]+w[i])) for j in range(A+1)])
        )))))
def p_liquidity14d_liq_2(i):
    t_awq_list0 = [t_awq_m_j for t_awq_m in t_aw_q0 for t_awq_m_j in t_awq_m]; t_awq_list1 = [t_awq_m_j for t_awq_m in t_aw_q1 for t_awq_m_j in t_awq_m]; 
    return And(
        Exists([xa_q], And(user_is_legit(xa_q), b[i]==True,
            ForAll([xn_q0, f_q0, w_q0, *aw_q0, *t_w_q0, *t_awq_list0, block_num_q0, pay_amount_q0, b_q0, *t_b_q0, xn_q1, f_q1, w_q1, *aw_q1, *t_w_q1, *t_awq_list1, block_num_q1, pay_amount_q1, b_q1, *t_b_q1],  
                Or(
Not(step_trans(f_q0, xa_q, xn_q0, pay_amount_q0, aw[i], aw_q0, w[i], w_q0, t_aw_q0, t_w_q0, block_num[i], block_num_q0, i+0, b[i], b_q0, t_b_q0)),
Not(step_trans(f_q1, xa_q, xn_q1, pay_amount_q1, aw_q0, aw_q1, w_q0, w_q1, t_aw_q1, t_w_q1, block_num_q0, block_num_q1, i+1, b_q0, b_q1, t_b_q1)),

And([Or(j != xa_q, Not(aw_q1[j] == aw[i][j]+w[i])) for j in range(A+1)])
        )))))

queries = {}
queries['liquidity14d_liq'] = [[p_liquidity14d_liq_1(i),p_liquidity14d_liq_2(i)] for i in range(1, N)]
queries['liquidity14c_liq'] = [[p_liquidity14c_liq_1(i),p_liquidity14c_liq_2(i)] for i in range(1, N)]


timeStart = time.time()
for prop in {'liquidity14d_liq','liquidity14c_liq'}:
    print()
    print('Property [' + prop + ']')
    for i, q in enumerate(queries[prop]):
        print("	i:" , i)
        liquid = False
        for j in range(0, len(q)):
            print("		j:", j)
            qj = q[j] 
            s2 = Solver()
            s2.add(s.assertions())
            s2.add(qj)
            text= s2.to_smt2()

            resj = s.check(qj)
            print("		resj =", resj)
            #print(s.reason_unknown())

            resj2 = s2.check()
            print("		resj2 =", resj2)
            #print(s.reason_unknown())

            if resj == unsat or resj2 == unsat:      
            #if resj == unsat:
                liquid = True
                break
        #if not liquid:     # commented for debugging
        #    break
    if not liquid: print("not liquid [in 2 steps]")
    else: print("liquid [in 2 steps]")
    timeTot = time.time() - timeStart
    print("Solving time: " + str(timeTot) + "s")

# for i, q in enumerate(queries):
#     timeStart = time.time()
#     # print("q : ", q)
#     print("p " + str(i) + " : ", end='')
#     # sq = s
#     # sq.add(q)
#     # print("\n\nsq:", sq, "\n\n")
#     res = s.check(q)
#     if res == sat:
#         print(" sat (=> not liquid)")
#         m = s.model()
#         # print(m)
#         #printState(m)
#         # exit()
#     else:
#         print(" unsat (=> liquid)")

#     timeTot = time.time() - timeStart
#     print("Solving time: " + str(timeTot) + "s")
                      

