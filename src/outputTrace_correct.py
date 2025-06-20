
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
N = 5

# A = upper bound on the number of actors (A+1)
A = 2

# Maximum functions depth
M = 50

# Contract's balance
w = [Int("w_%s" % (i)) for i in range(N+1)]
w_q0 = Int("wq0")


# Block number
block_num = [Int("block_num_%s" % (i)) for i in range(N+1)]
err = [Bool("err_%s" % (i)) for i in range(N+1)]
err_q0 = Bool("err_q0")


Proc = Datatype('Proc')
Proc.declare('pay_func')
Proc.declare('coinbase')
Proc.declare('unlock_func')

Proc = Proc.create()

# Contract's state variables

lock = [Bool("lock_%s" % (i)) for i in range(N+1)]
t_lock = [[Bool("t_lock_%s_%s" % (i, m)) for m in range(M)] for i in range(N+1)]
lock_q0 = Bool("lockq0")
t_lock_q0 = [Bool("t_lockq0_%s" % (m)) for m in range(M)]

# Called procedure
f = [Const("f_%s" % (i), Proc) for i in range(N+1)]
f_q0 = Const("f_q0", Proc)


# users' wallets
aw = [[Int("aw_%s_%s" % (i, j)) for j in range(A+1)] for i in range(N+1)]
aw_q0 = [Int("awq0_%s" % j) for j in range(A+1)]


# msg.sender
xa = [Int("xa_%s" % (i)) for i in range(N+1)]
xa_q = Int("xa_q")

# msg.value
xn = [Int("xn_%s" % (i)) for i in range(N+1)]
xn_q0 = Int("xn_q0")


# functions args
pay_func_amount = [Int("pay_func_amount_%s" % (i)) for i in range(N+1)]
pay_func_amount_q0 = Int("pay_func_amount0_q")

# List of ids hard coded
hard_coded_list = [0]

# Temporary contract balance. Used inside functions to model internal states
t_w = [[Int("t_w_%s_%s" % (i, m)) for m in range(M)] for i in range(N+1)]
t_w_q0 = [Int("t_wq0_%s" % (m)) for m in range(M)]
 

# Temporary users wallets
t_aw = [[[Int("t_aw_%s_%s_%s" % (i, m, j)) for j in range(A+1)]
         for m in range(M)] for i in range(N+1)]

t_aw_q0 = [[Int("t_awq0_%s_%s" % (m, j)) for j in range(A+1)] for m in range(M)]


s = Solver()

def next_state_tx(aw1, aw2, w1, w2, lockNow, lockNext):
    return And(w2 == w1,
               And([aw2[j] == aw1[j] for j in range(A+1)])
               , lockNow==lockNext
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

def constructor(xa1, xn1, awNow, awNext, wNow, wNext, t_aw, t_w, block_num, lockNow, lockNext, t_lock, err):
    return And(xn1 == 0, 
	And(t_lock[0] == True, err==False, True, next_state_tx(awNow, awNext, wNow, wNext, t_lock[0], lockNext)))

def unlock_func(xa1, xn1, awNow, awNext, wNow, wNext, t_aw, t_w, block_num, lockNow, lockNext, t_lock, err):
    return And(t_w[0] == wNow + xn1, 
	And(And(
	True,
	t_lock[0] == False), err == Or(False, Not(And(lockNow,xn1 == 2000))), True, Or(And(err==True, next_state_tx(awNow, awNext, wNow, wNext, lockNow, lockNext)), And(err==False, next_state_tx(awNow, awNext, t_w[0], wNext, t_lock[0], lockNext)))))

def pay_func(xa1, xn1, pay_func_amount, awNow, awNext, wNow, wNext, t_aw, t_w, block_num, lockNow, lockNext, t_lock, err):
    return And(True, 
	And(And(
	True,
	send(xa1, pay_func_amount, wNow, t_w[0], awNow, t_aw[0])), err == Or(False, Not(pay_func_amount>= 0), Not(xn1==0), Not(Not(lockNow))), True, Or(And(err==True, next_state_tx(awNow, awNext, wNow, wNext, lockNow, lockNext)), And(err==False, next_state_tx(t_aw[0], awNext, t_w[0], wNext, lockNow, lockNext)))))

def coinbase(xa1, xn1, awNow, awNext, wNow, wNext, t_aw, t_w, block_num, lockNow, lockNext, t_lock, err):
	return And(err == False, t_w[0] == wNow + xn1, next_state_tx(awNow, awNext, t_w[0], wNext, lockNow, lockNext))


def user_is_legit(xa1):
    return And(xa1 >= 1, xa1 <= A)


def user_has_not_already_played(xa, xa1, f, i):
    return Not(Or([And(xa[k] == xa1, f[k] == Proc.pay) for k in range(i)]))


def user_is_not_hard_coded(xa1):
    return Not(Or([xa1 == hc_i for hc_i in hard_coded_list]))


def user_is_fresh(xa, xa1, f, i):
    return And(user_is_not_hard_coded(xa1), user_has_not_already_played(xa, xa1, f, i))

# transition rules

def step_trans(f1, xa1, xn1, pay_func_amount, aw1, aw2, w1, w2, t_aw, t_w, block_num1, block_num2, i, lockNow, lockNext, t_lock, err):
    return And(And(xn1 >= 0, w2 >= 0),
               And([aw1[j] >= 0 for j in range(A+1)]),
               block_num2 >= block_num1,
               
               	If(f1 == Proc.coinbase, And(xa1 == 0, 
	coinbase(xa1, xn1, aw1, aw2, w1, w2, t_aw, t_w, block_num1, lockNow, lockNext, t_lock, err)),
And(xa1 >= 1, xa1 <= A, 	If(f1 == Proc.unlock_func,
		unlock_func(xa1, xn1, aw1, aw2, w1, w2, t_aw, t_w, block_num1, lockNow, lockNext, t_lock, err),
			pay_func(xa1, xn1, pay_func_amount, aw1, aw2, w1, w2, t_aw, t_w, block_num1, lockNow, lockNext, t_lock, err)))))

# initial state
s.add(w[0] >= 0)
               
new_state = And(And(xa[0] >= 0, xa[0] <= A, xn[0] >= 0),
               And([aw[0][j] >= 0 for j in range(A+1)]),
                  constructor(xa[0], xn[0],  aw[0], aw[1], w[0], w[1], t_aw[0], t_w[0], block_num[0], lock[0], lock[1], t_lock[0], err[1]))
s.add(new_state)
for i in range(1, N):
    new_state = step_trans(f[i], xa[i], xn[i], pay_func_amount[i], aw[i],
                           aw[i+1], w[i], w[i+1], t_aw[i], t_w[i], block_num[i], block_num[i+1], i, lock[i], lock[i+1], t_lock[i], err[i+1])
    s.add(new_state)


# print(s)

# def p(i):
#     t_awq_list = [t_awq_m_j for t_awq_m in t_aw_q for t_awq_m_j in t_awq_m]
#     #print([xn_q, f_q, w_q, *aw_q, *t_w_q, *t_awq_list ])
#     return And(w[i] > 0,
#                Exists([xa_q], And(user_is_legit(xa_q), user_is_fresh(xa, xa_q, f,  i),
#                       ForAll([xn_q, f_q, w_q, *aw_q, *t_w_q, *t_awq_list, pay_func_amount_q, lock_q, *t_lock_q ], Or(Not(step_trans(f_q, xa_q, xn_q, pay_func_amount_q, aw[i], aw_q, w[i], w_q, t_aw_q, t_w_q, i, lock[i], lock_q, t_lock_q)), w_q > 0)))))
#                       #ForAll([xn_q, f_q, w_q, *aw_q ], Or(Not(step_trans(f_q, xa_q, xn_q, aw[i], aw_q, w[i], w_q, t_aw[i], t_w[i], i)), w_q > 0)))))



def p_wd1_nonliquid_1(i):
    t_awq_list0 = [t_awq_m_j for t_awq_m in t_aw_q0 for t_awq_m_j in t_awq_m]; 
    return And(
        Exists([xa_q], And(user_is_legit(xa_q), And(w[i]>=1,lock[i]),
            ForAll([xn_q0, f_q0, w_q0, *aw_q0, *t_w_q0, *t_awq_list0, err_q0, pay_func_amount_q0, lock_q0, *t_lock_q0],  
                Or(
Not(step_trans(f_q0, xa_q, xn_q0, pay_func_amount_q0, aw[i], aw_q0, w[i], w_q0, t_aw_q0, t_w_q0, block_num[i], block_num[i], i+0, lock[i], lock_q0, t_lock_q0, err_q0)),

Not(And([Or(j != xa_q, aw_q0[j] >= (aw[i][j]+1)) for j in range(A+1)]))
        )))))

def p_unlock_nonliquid_1(i):
    t_awq_list0 = [t_awq_m_j for t_awq_m in t_aw_q0 for t_awq_m_j in t_awq_m]; 
    return And(
        Exists([xa_q], And(user_is_legit(xa_q), And(And(w[i]>=1,lock[i]),And([Or(j != xa_q, aw[i][j] >= 1000) for j in range(A+1)])),
            ForAll([xn_q0, f_q0, w_q0, *aw_q0, *t_w_q0, *t_awq_list0, err_q0, pay_func_amount_q0, lock_q0, *t_lock_q0],  
                Or(
Not(step_trans(f_q0, xa_q, xn_q0, pay_func_amount_q0, aw[i], aw_q0, w[i], w_q0, t_aw_q0, t_w_q0, block_num[i], block_num[i], i+0, lock[i], lock_q0, t_lock_q0, err_q0)),

Not(lock_q0 == False)
        )))))

def p_unlock_liquid_1(i):
    t_awq_list0 = [t_awq_m_j for t_awq_m in t_aw_q0 for t_awq_m_j in t_awq_m]; 
    return And(
        Exists([xa_q], And(user_is_legit(xa_q), And(And(w[i]>=1,lock[i]),And([Or(j != xa_q, aw[i][j] >= 2000) for j in range(A+1)])),
            ForAll([xn_q0, f_q0, w_q0, *aw_q0, *t_w_q0, *t_awq_list0, err_q0, pay_func_amount_q0, lock_q0, *t_lock_q0],  
                Or(
Not(step_trans(f_q0, xa_q, xn_q0, pay_func_amount_q0, aw[i], aw_q0, w[i], w_q0, t_aw_q0, t_w_q0, block_num[i], block_num[i], i+0, lock[i], lock_q0, t_lock_q0, err_q0)),

Not(lock_q0 == False)
        )))))



queries = {}
queries['wd1_nonliquid'] = [[p_wd1_nonliquid_1(i)] for i in range(1, N+1)]
queries['unlock_liquid'] = [[p_unlock_liquid_1(i)] for i in range(1, N+1)]
queries['unlock_nonliquid'] = [[p_unlock_nonliquid_1(i)] for i in range(1, N+1)]


for prop in {'wd1_nonliquid','unlock_liquid','unlock_nonliquid'}:
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
# for prop in {'wd1_nonliquid','unlock_liquid','unlock_nonliquid'}:
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
#     if not liquid: print("not liquid [in 1 steps]")
#     else: print("liquid [in 1 steps]")
#     timeTot = time.time() - timeStart
#     print("Solving time: " + str(timeTot) + "s")
               
