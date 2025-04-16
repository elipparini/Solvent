import copy
from antlr4 import *
from TxScriptLexer import *
from TxScriptParser import *
from TxScriptVisitor import *
import re

class Kind2Visitor(TxScriptVisitor):
    def __init__(self, N, A, Trace_Based, can_transations_arrive_any_time, fixed_iteration):
        self.__proc = set()
        self.__proc_args = {}
        self.__add_last_cmd = False
        self.__prefix = ''
        self.__functions = {}
        self.__functions_prop = {}
        self.__args_map = {}
        self.__nesting_w = 0
        self.__nesting_aw = 0
        self.__max_nesting = -1
        self.__globals = []
        self.__globals_index = {}
        self.__globals_index_max = {}
        self.__globals_const = {}
        self.__globals_modifier = -1
        self.__initial_const_globals = {}
        self.__visit_properties = False
        self.__visit_properties_body = False
        self.__requires = set()
        self.__const = False
        self.__tx_sender = 'xa'
        self.__prop_nested_i = set()
        self.__n_transactions = 1
        self.__max_n_transactions = 1
        self.__prop_transactions = {}
        self.__pi = 1
        self.__prop_name = ''
        self.__prop_names = set()
        self.__maps = set()
        # N = upper bound on the length of trace
        self.__N = N
        # A = upper bound on the number of actors (A+1)
        self.__A = A
        self.__M = -1
        self.__Trace_Based = Trace_Based
        self.__can_transations_arrive_any_time = can_transations_arrive_any_time
        self.__fixed_iteration = fixed_iteration
        self.__defaultAddress = 0
        self.__ctx = None
        self.__payable = False
        self.__not_valid_names = ['sender', 'msg.sender', 'value', 'msg.value', 'balance']
        if not self.__fixed_iteration == -1:
            self.__N = fixed_iteration

    # Visit a parse tree produced by TxScriptParser#contractExpr.
    def visitContractExpr(self, ctx:TxScriptParser.ContractExprContext):
        decls = self.visit(ctx.decl)
        decls = [decl for decl in decls if decl is not None]
        # Properties commented for now!
        self.__visit_properties = True
        self.__ctx = ctx.decl
        props = self.visit(ctx.properties)
        self.__visit_properties = False

        # self.__visit_properties = False
        self.__nesting_w = 1
        self.__nesting_aw = 1
        self.__t_curr_w = 't_w_0'
        self.__t_new_w = 't_w_1'
        self.__t_curr_a = ['awNow'] * self.__A
        self.__t_new_a = ['t_aw_0'] * self.__A
        
        for k in self.__globals_index:
            self.__globals_index[k] = 0

        # Coinbase part, commented for now!
        # if self.__can_transations_arrive_any_time and not any('coinbase' in decl for decl in decls):
        #     decls.append('\ndef coinbase(xa1, xn, awNow, awNext, wNow, wNext, t_aw, t_w, block_num{global_args}, err):\n\treturn And(err == False, t_w[0] == wNow + xn, next_state_tx(awNow, awNext, t_w[0], wNext{global_args_next_state_tx}))'.format(
        #         global_args = (', ' + ', '.join([g.text+'Now, '+g.text+'Next, t_'+g.text for (g, _) in self.__globals])) if self.__globals else '', 
        #         # global_args_assign = (', '.join([g.text+'Next == '+g.text+'Next' for (g, _) in self.__globals]) + ', ') if self.__globals else ''), 
        #         global_args_next_state_tx = (', ' + ', '.join([(g.text + 'Now' if self.__globals_index[g.text]+self.__globals_modifier < 0 else 't_'+g.text + '['+str(self.__globals_index[g.text]+self.__globals_modifier)+']')+', '+g.text+'Next' for (g, _) in self.__globals])) if self.__globals else ''
        #     ))
        #     self.__proc.add('coinbase')
        #     self.__proc_args['coinbase'] = None
        
        functions = ','.join([f'{p}' for p in self.__proc if p != 'constructor'])
        contract_args = ['{a}:{t}'.format(a=self.__args_map[a][0], t=self.__args_map[a][1]).replace('address', 'int') for a in self.__args_map if self.__args_map[a][1] != 'hash']
        contract_args = ';'.join(
            ['xa:int', 'xn:int', 'f:functions'] + 
            contract_args + 
            ['starting_w: int', 'starting_aw_1: int', 'starting_aw_2: int']) 
        contract_assumptions = '\n'.join([f'assume starting_aw_{ag} >= 0;' for ag in range(1, self.__A+1)])
        contract_globals = ['var contract_not_constructed: bool;']
        for (g_var,g_type) in self.__globals:
            if g_type == ('MapAddr', 'int'):
                g_init_value = self.__initial_const_globals[g_var.text]
                contract_globals += [f'const starting_{g_var.text}_{ag} : int = {g_init_value};' for ag in range(1, self.__A+1)]
            else:
                if g_type == 'Address' or g_type == 'Hash' or g_type == 'Secret':
                    g_type = 'int'
                g_init_value = self.__initial_const_globals[g_var.text]
                contract_globals += [f'const starting_{g_var.text} : {g_type} = {g_init_value};']
            # I assume that the visit of the constructor has generated such information
        contract_globals += ['var w: int;']
        contract_globals += [f'var w_{i}: int;' for i in range(self.__max_nesting + 1)]
        contract_globals += [f'var aw_{ag}: int;' for ag in range(1, self.__A+1)]
        contract_globals += [f'var aw_{ag}_{i}: int;' for ag in range(1, self.__A+1) for i in range(self.__max_nesting + 1)]
        for (g_var,g_type) in self.__globals:
            if g_type == ('MapAddr', 'int'):
                contract_globals += [f'var {g_var.text}_{ag} : int;' for ag in range(1, self.__A+1)]
                contract_globals += [f'var {g_var.text}_{ag}_{i} : int;' for i in range(self.__globals_index_max[g_var.text]) for ag in range(1, self.__A+1)]
            else:
                if g_type == 'Address' or g_type == 'Hash' or g_type == 'Secret':
                    g_type = 'int'
                contract_globals += [f'var {g_var.text} : {g_type};']
                contract_globals += [f'var {g_var.text}_{i} : {g_type};' for i in range(self.__globals_index_max[g_var.text])]
        contract_globals = '\n'.join(contract_globals)
        
        #commented out because args now are a single variable in the lus input
        # args = ['{a} = [int("{a}_%s" % (i)) for i in range(N+1)]'.format(a=self.__args_map[a][0]) for a in self.__args_map if self.__args_map[a][1] != 'hash']
        # for i in range(0, self.__max_n_transactions):
        #     args += ['{a}_q{i} = int("{a}{i}_q")'.format(i=i, a=self.__args_map[a][0]) for a in self.__args_map if self.__args_map[a][1] != 'hash']
        # step_trans_args = [self.__args_map[a][0] for a in self.__args_map if 'constructor' not in self.__args_map[a][0] if self.__args_map[a][1] != 'hash']
        
        # commented out because related to property
        # t_aw_qs = ''
        # for i in range(0, self.__max_n_transactions):
        #     t_aw_qs += f't_aw_q{i} = [[int("t_awq{i}_%s_%s" % (m, j)) for j in range(A+1)] for m in range(M)]\n'
        
        # commented out for now because related to property
        # xn_qs = ''
        # f_qs = ''
        # w_qs = ''
        # aw_qs = ''
        # t_w_qs = ''
        # err_qs = ''
        # for i in range(0, self.__max_n_transactions):
        #     # block_num_qs += f'block_num_q{i} = int("block_num_q{i}")\n'
        #     xn_qs += f'xn_q{i} = int("xn_q{i}")\n'
        #     f_qs += f'f_q{i} = Const("f_q{i}", Proc)\n'
        #     w_qs += f'w_q{i} = int("wq{i}")\n'
        #     aw_qs += f'aw_q{i} = [int("awq{i}_%s" % j) for j in range(A+1)]\n'
        #     t_w_qs += f't_w_q{i} = [int("t_wq{i}_%s" % (m)) for m in range(M)]\n'
        #     err_qs += f'err_q{i} = Bool("err_q{i}")\n'
        body = ''
        n_tabs = 0
        keys = list(self.__proc_args.keys())
        keys.append('dummy')
        if 'constructor' in keys: keys.remove('constructor')
        if keys:
            aux = 1
            # go back on coinbase aspect!!
            # if 'coinbase' in keys:
            #     functions_call += '\tIf(f1 == Proc.coinbase, And(xa1 == 0, \n'
            #     n_tabs += 1
            #     functions_call += '\t'*n_tabs + 'coinbase' + '(xa1, xn, ' + (','.join(self.__proc_args['coinbase'])+', ' if self.__proc_args['coinbase'] else '') + 'aw1, aw2, w1, w2, t_aw, t_w, block_num1' + ((', ' + ', '.join([g.text+'Now, '+g.text+'Next, t_'+g.text for (g, _) in self.__globals])) if self.__globals else '') + ', err)),\n'
            #     keys.remove('coinbase')
            #     aux += 1
            # functions_call += 'And(xa1 >= 1, xa1 <= A, '
            if not self.__visit_properties:
                body = 'if (true -> pre contract_not_constructed) then\n' + self.__functions['constructor'] + '\n' 
            for p in keys[:-1]:
                if self.__visit_properties and p == keys[0]:
                    cmd = 'if'
                else:
                    cmd = 'elsif'
                body += '\t'*n_tabs + cmd + ' f = ' + p + ' then\n'
                n_tabs += 1
                body += f'\t{self.__functions[p]}\n'
                # functions_call += '\t'*n_tabs + p + '(xa1, xn, ' + (','.join(self.__proc_args[p])+', ' if self.__proc_args[p] else '') + 'aw1, aw2, w1, w2, t_aw, t_w, block_num1' + ((', ' + ', '.join([g.text+'Now, '+g.text+'Next, t_'+g.text for (g, _) in self.__globals])) if self.__globals else '') + ', err),\n'
            n_tabs += 1
            body += 'else'
            same = f'\n\tw = (starting_w -> pre w);'
            same += '\n\t' + '\n\t'.join([f'aw_{i} = (starting_aw_{i} -> pre aw_{i});' for i in range(1, self.__A+1)])
            # same += '\n\t' + '\n\t'.join([g.text + ' = ' + f'(starting_{g.text} -> pre {g.text});' for (g, _) in self.__globals]) if self.__globals else ''
            aux = '\n\t'.join([g.text + ' = ' + f'(starting_{g.text} -> pre {g.text});' for (g, ty) in self.__globals if ty != ('MapAddr', 'int')]) if self.__globals else ''
            same += '\n\t' + (aux if aux else '')
            aux = '\n\t'.join([g.text + f'_{ag} = ' + f'(starting_{g.text}_{ag} -> pre {g.text}_{ag});' for ag in range(1, self.__A+1) for (g, ty) in self.__globals if ty == ('MapAddr', 'int')]) if self.__globals else ''
            same += '\n\t' + (aux if aux else '')
            body += f'{same}\n'
            # body += f'\t{self.__functions[keys[-1]]}\n'
            # functions_call += '\t'*n_tabs + keys[-1] + '(xa1, xn, ' + (','.join(self.__proc_args[keys[-1]])+', ' if self.__proc_args[keys[-1]] else '') + 'aw1, aw2, w1, w2, t_aw, t_w, block_num1' + ((', ' + ', '.join([g.text+'Now, '+g.text+'Next, t_'+g.text for (g, _) in self.__globals])) if self.__globals else '') + ', err)'
            body += 'fi'
        all_props = '\n'.join([prop for prop in props])
        res = f'''
type functions = enum {{ dummy, {functions} }};
node {ctx.name.text.lower()} ({contract_args}) returns();
(*@contract
    assume starting_w >= 0;
    {contract_assumptions}
*)
{contract_globals}
let
    {body}
    {all_props}
tel
        '''.replace('skip and', 'true and').replace('and skip', 'and true').replace('skip', '').replace(';;', ';')
        
        return res 


    # Visit a parse tree produced by TxScriptParser#constFieldDecl.
    # def visitConstFieldDecl(self, ctx:TxScriptParser.ConstFieldDeclContext):
    #     self.__const = True
    #     self.visit(ctx.child)
    #     self.__const = False


    # Visit a parse tree produced by TxScriptParser#declsExpr.
    def visitDeclsExpr(self, ctx:TxScriptParser.DeclsExprContext):
        decls = []
        for decl in ctx.declExpr():
            self.__M = -1
            decls.append(self.visit(decl))
            self.__max_nesting = max(self.__M, self.__max_nesting)
            for k in self.__globals_index:
                if k not in self.__globals_index_max:
                    self.__globals_index_max[k] = self.__globals_index[k]
                self.__globals_index_max[k] = max(self.__globals_index_max[k], self.__globals_index[k])
        return decls
    

    # Visit a parse tree produced by TxScriptParser#propertiesExpr.
    def visitPropertiesExpr(self, ctx:TxScriptParser.PropertiesExprContext):
        props = []
        for prop in ctx.propertyExpr():
            props.append(self.visit(prop))
        return props


    # Visit a parse tree produced by TxScriptParser#propertyExpr.
    def visitPropertyExpr(self, ctx:TxScriptParser.PropertyExprContext):
        self.__prop_name = ctx.name.text
        self.__prop_names.add(self.__prop_name)
        return self.visit(ctx.phi)


    # Visit a parse tree produced by TxScriptParser#hashDecl.
    def visitHashDecl(self, ctx:TxScriptParser.HashDeclContext):
        if self.__visit_properties: return
        if ctx.var.text in self.__not_valid_names:
            raise Exception(f'{ctx.var.text} is not a valid name for a field, please choose a different name')
        self.__globals.append((ctx.var, 'Hash'))
        self.__globals_index[ctx.var.text] = 0
        self.__globals_const[ctx.var.text] = self.__const


    # Visit a parse tree produced by TxScriptParser#secretDecl.
    def visitSecretDecl(self, ctx:TxScriptParser.SecretDeclContext):
        if self.__visit_properties: return
        if ctx.var.text in self.__not_valid_names:
            raise Exception(f'{ctx.var.text} is not a valid name for a field, please choose a different name')
        self.__globals.append((ctx.var, 'Secret'))
        self.__globals_index[ctx.var.text] = 0
        self.__globals_const[ctx.var.text] = True if ctx.const else False #self.__const


    # Visit a parse tree produced by TxScriptParser#intDecl.
    def visitIntDecl(self, ctx:TxScriptParser.IntDeclContext):
        if self.__visit_properties: return
        if ctx.var.text in self.__not_valid_names:
            raise Exception(f'{ctx.var.text} is not a valid name for a field, please choose a different name')
        self.__globals.append((ctx.var, 'int'))
        self.__globals_index[ctx.var.text] = 0
        self.__globals_const[ctx.var.text] = True if ctx.const else False #self.__const


    # Visit a parse tree produced by TxScriptParser#boolDecl.
    def visitBoolDecl(self, ctx:TxScriptParser.BoolDeclContext):
        if self.__visit_properties: return
        if ctx.var.text in self.__not_valid_names:
            raise Exception(f'{ctx.var.text} is not a valid name for a field, please choose a different name')
        self.__globals.append((ctx.var, 'bool'))
        self.__globals_index[ctx.var.text] = 0
        self.__globals_const[ctx.var.text] = True if ctx.const else False #self.__const


    # Visit a parse tree produced by TxScriptParser#strDecl.
    def visitStrDecl(self, ctx:TxScriptParser.StrDeclContext):
        if self.__visit_properties: return
        if ctx.var.text in self.__not_valid_names:
            raise Exception(f'{ctx.var.text} is not a valid name for a field, please choose a different name')
        self.__globals.append((ctx.var, 'String'))
        self.__globals_index[ctx.var.text] = 0
        self.__globals_const[ctx.var.text] = True if ctx.const else False #self.__const


    # Visit a parse tree produced by TxScriptParser#addrDecl.
    def visitAddrDecl(self, ctx:TxScriptParser.AddrDeclContext):
        if self.__visit_properties: return
        if ctx.var.text in self.__not_valid_names:
            raise Exception(f'{ctx.var.text} is not a valid name for a field, please choose a different name')
        self.__globals.append((ctx.var, 'Address'))
        self.__globals_index[ctx.var.text] = 0
        self.__globals_const[ctx.var.text] = True if ctx.const else False #self.__const


    # Visit a parse tree produced by TxScriptParser#mapAddrDecl.
    def visitMapAddrDeclInt(self, ctx:TxScriptParser.MapAddrDeclIntContext):
        if self.__visit_properties: return
        if ctx.var.text in self.__not_valid_names:
            raise Exception(f'{ctx.var.text} is not a valid name for a field, please choose a different name')
        self.__globals.append((ctx.var, ('MapAddr', 'int')))
        # for i in range(1, self.__A+1):
        self.__globals_index[ctx.var.text] = 0
        self.__maps.add(ctx.var.text)
        self.__globals_const[ctx.var.text] = True if ctx.const else False #self.__const


    # Visit a parse tree produced by TxScriptParser#constrDecl.
    def visitConstrDecl(self, ctx:TxScriptParser.ConstrDeclContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TxScriptParser#nonPayableConstructorDecl.
    def visitNonPayableConstructorDecl(self, ctx:TxScriptParser.NonPayableConstructorDeclContext):
        self.__nesting_w = 0
        self.__nesting_aw = 0
        if self.__visit_properties:
            self.__t_curr_w = 'w'
            self.__t_new_w = 'w_0_nx'
            self.__t_curr_a = [f'aw_{i}' for i in range(self.__A+1)]
            self.__t_new_a = [f'aw_{i}_0_nx' for i in range(self.__A+1)]
        else:
            self.__t_curr_w = '(starting_w -> pre w)'
            self.__t_new_w = 'w_0'
            self.__t_curr_a = [f'(starting_aw_{i} -> pre aw_{i})' for i in range(self.__A+1)]
            self.__t_new_a = [f'aw_{i}_0' for i in range(self.__A+1)]
        self.__proc.add('constructor')
        self.__prefix = 'constructor'
        for k in self.__globals_index:
            self.__globals_index[k] = 0
        self.__requires = set()
        if not self.__visit_properties: 
            self.__requires.add('xn=0')
            self.__requires.add('(' + ' or '.join([f'xa = {i}' for i in range(1, self.__A+1)]) + ')')
        else:
            self.__requires.add('xn_tx=0')
            self.__requires.add('(' + ' or '.join([f'xa_tx = {i}' for i in range(1, self.__A+1)]) + ')')
        return self.visitFun(ctx, '')
    

    # Visit a parse tree produced by TxScriptParser#payableConstructorDecl.
    def visitPayableConstructorDecl(self, ctx:TxScriptParser.PayableConstructorDeclContext):
        self.__payable = True
        self.__nesting_w = 1
        self.__nesting_aw = 1
        if self.__visit_properties:
            self.__t_curr_w = 'w'
            self.__t_new_w = 'w_0_nx'
            self.__t_curr_a = [f'aw_{i}' for i in range(self.__A+1)]
            self.__t_new_a = [f'aw_{i}_0_nx' for i in range(self.__A+1)]
        else:
            self.__t_curr_w = '(starting_w -> pre w)'
            self.__t_new_w = 'w_0'
            self.__t_curr_a = [f'(starting_aw_{i} -> pre aw_{i})' for i in range(self.__A+1)]
            self.__t_new_a = [f'aw_{i}_0' for i in range(self.__A+1)]
        self.__proc.add('constructor')
        self.__prefix = 'constructor'
        for k in self.__globals_index:
            self.__globals_index[k] = 0
        self.__requires = set()
        err = 'err' + '_' + str(self.__globals_index['err'])
        err1 = 'err' + '_' + str(self.__globals_index['err']-1) if self.__globals_index['err'] > 0 else 'false'
        self.__globals_index['err'] += 1
        if not self.__visit_properties: 
            req1 = '(' + ' or '.join([f'xa = {i}' for i in range(1, self.__A+1)]) + ')'
            req2 = '(' + ' and '.join([f'(not(xa = {i}) or (starting_aw_{i} -> pre aw_{i}) >= xn)' for i in range(1, self.__A+1)]) + ')'
            req = f'if (not(xn >= 0 and {req1} and {req2})) then {err}=true; else {err}={err1}; fi\n'
            # self.__requires.add('xn >= 0')
            # self.__requires.add('(' + ' or '.join([f'xa = {i}' for i in range(1, self.__A+1)]) + ')')
            # self.__requires.add('(' + ' and '.join([f'(not(xa = {i}) or (starting_aw_{i} -> pre aw_{i}) >= xn)' for i in range(1, self.__A+1)]) + ')')
            add_to_body = req + self.send('xa', 'xn', negative=True)
            self.__t_curr_a = [f'aw_{i}_{self.__nesting_aw-1}' for i in range(self.__A+1)]
            self.__t_new_a = [f'aw_{i}_{self.__nesting_aw}' for i in range(self.__A+1)]
            self.__t_curr_w = 'w_' + str(self.__nesting_w-1)
            self.__t_new_w = 'w_' + str(self.__nesting_w)
        else:
            req1 = '(' + ' or '.join([f'xa_tx = {i}' for i in range(1, self.__A+1)]) + ')'
            req2 = '(' + ' and '.join([f'(not(xa_tx = {i}) or aw_{i} >= xn_tx)' for i in range(1, self.__A+1)]) + ')'
            err1 = err1+'_nx' if err1 != 'false' else err1
            req = f'(if (not(xn_tx >= 0 and {req1} and {req2})) then {err}_nx=true else {err}={err1})\n'
            # self.__requires.add('xn_tx >= 0')
            # self.__requires.add('(' + ' or '.join([f'xa_tx = {i}' for i in range(1, self.__A+1)]) + ')')
            # self.__requires.add('(' + ' and '.join([f'(not(xa_tx = {i}) or aw_{i} >= xn_tx)' for i in range(1, self.__A+1)]) + ')')
            add_to_body = req + ' and (' + self.send('xa_tx', 'xn_tx', negative=True) + ')'
            self.__t_curr_a = [f'aw_{i}_{self.__nesting_aw-1}_nx' for i in range(self.__A+1)]
            self.__t_new_a = [f'aw_{i}_{self.__nesting_aw}_nx' for i in range(self.__A+1)]
            self.__t_curr_w = 'w_' + str(self.__nesting_w-1) + '_nx'
            self.__t_new_w = 'w_' + str(self.__nesting_w) + '_nx'
        self.__M += 1        
        return self.visitFun(ctx, add_to_body)


    # Visit a parse tree produced by TxScriptParser#payableFunDecl.
    def visitPayableFunDecl(self, ctx:TxScriptParser.PayableFunDeclContext):
        self.__payable = True
        self.__nesting_w = 1
        self.__nesting_aw = 1
        if self.__visit_properties:
            self.__t_curr_w = 'w'
            self.__t_new_w = 'w_0_nx'
            self.__t_curr_a = [f'aw_{i}' for i in range(self.__A+1)]
            self.__t_new_a = [f'aw_{i}_0_nx' for i in range(self.__A+1)]
        else:
            self.__t_curr_w = '(starting_w -> pre w)'
            self.__t_new_w = 'w_0'
            self.__t_curr_a = [f'(starting_aw_{i} -> pre aw_{i})' for i in range(self.__A+1)]
            self.__t_new_a = [f'aw_{i}_0' for i in range(self.__A+1)]
        self.__proc.add(ctx.name.text + '_func')
        self.__prefix = ctx.name.text + '_func'
        for k in self.__globals_index:
            self.__globals_index[k] = 0
        self.__requires = set()
        err = 'err' + '_' + str(self.__globals_index['err'])
        err1 = 'err' + '_' + str(self.__globals_index['err']-1) if self.__globals_index['err'] > 0 else 'false'
        self.__globals_index['err'] += 1
        if not self.__visit_properties: 
            req1 = '(' + ' or '.join([f'xa = {i}' for i in range(1, self.__A+1)]) + ')'
            req2 = '(' + ' and '.join([f'(not(xa = {i}) or (starting_aw_{i} -> pre aw_{i}) >= xn)' for i in range(1, self.__A+1)]) + ')'
            req = f'if (not(xn >= 0 and {req1} and {req2})) then {err}=true; else {err}={err1}; fi\n'
            # self.__requires.add('xn >= 0')
            # self.__requires.add('(' + ' or '.join([f'xa = {i}' for i in range(1, self.__A+1)]) + ')')
            # self.__requires.add('(' + ' and '.join([f'(not(xa = {i}) or (starting_aw_{i} -> pre aw_{i}) >= xn)' for i in range(1, self.__A+1)]) + ')')
            add_to_body = req + self.send('xa', 'xn', negative=True)
            self.__t_curr_a = [f'aw_{i}_{self.__nesting_aw-1}' for i in range(self.__A+1)]
            self.__t_new_a = [f'aw_{i}_{self.__nesting_aw}' for i in range(self.__A+1)]
            self.__t_curr_w = 'w_' + str(self.__nesting_w-1)
            self.__t_new_w = 'w_' + str(self.__nesting_w)
        else:
            req1 = '(' + ' or '.join([f'xa_tx = {i}' for i in range(1, self.__A+1)]) + ')'
            req2 = '(' + ' and '.join([f'(not(xa_tx = {i}) or aw_{i} >= xn_tx)' for i in range(1, self.__A+1)]) + ')'
            err1 = err1+'_nx' if err1 != 'false' else err1
            req = f'(if (not(xn_tx >= 0 and {req1} and {req2})) then {err}_nx=true else {err}_nx={err1})\n'
            # self.__requires.add('xn_tx >= 0')
            # self.__requires.add('(' + ' or '.join([f'xa_tx = {i}' for i in range(1, self.__A+1)]) + ')')
            # self.__requires.add('(' + ' and '.join([f'(not(xa_tx = {i}) or aw_{i} >= xn_tx)' for i in range(1, self.__A+1)]) + ')')
            add_to_body = req + ' and (' + self.send('xa_tx', 'xn_tx', negative=True) + ') and '
            self.__t_curr_a = [f'aw_{i}_{self.__nesting_aw-1}_nx' for i in range(self.__A+1)]
            self.__t_new_a = [f'aw_{i}_{self.__nesting_aw}_nx' for i in range(self.__A+1)]
            self.__t_curr_w = 'w_' + str(self.__nesting_w-1) + '_nx'
            self.__t_new_w = 'w_' + str(self.__nesting_w) + '_nx'
        self.__M += 1        
        return self.visitFun(ctx, add_to_body)


    # Visit a parse tree produced by TxScriptParser#nonPayableFunDecl.
    def visitNonPayableFunDecl(self, ctx:TxScriptParser.NonPayableFunDeclContext):
        self.__nesting_w = 0
        self.__nesting_aw = 0
        if self.__visit_properties:
            self.__t_curr_w = 'w'
            self.__t_new_w = 'w_0_nx'
            self.__t_curr_a = [f'aw_{i}' for i in range(self.__A+1)]
            self.__t_new_a = [f'aw_{i}_0_nx' for i in range(self.__A+1)]
        else:
            self.__t_curr_w = '(starting_w -> pre w)'
            self.__t_new_w = 'w_0'
            self.__t_curr_a = [f'(starting_aw_{i} -> pre aw_{i})' for i in range(self.__A+1)]
            self.__t_new_a = [f'aw_{i}_0' for i in range(self.__A+1)]
        self.__proc.add(ctx.name.text + '_func')
        self.__prefix = ctx.name.text + '_func'
        for k in self.__globals_index:
            self.__globals_index[k] = 0
        self.__requires = set()
        if not self.__visit_properties: 
            self.__requires.add('xn=0')
            self.__requires.add('(' + ' or '.join([f'xa = {i}' for i in range(1, self.__A+1)]) + ')')
        else:
            self.__requires.add('xn_tx=0')
            self.__requires.add('(' + ' or '.join([f'xa_tx = {i}' for i in range(1, self.__A+1)]) + ')')
        return self.visitFun(ctx, '')


    # Visit a parse tree produced by TxScriptParser#funDecl.
    def visitFun(self, ctx, add_to_body):
        args = self.visit(ctx.args)
        self.__add_last_cmd = True
        body = self.visit(ctx.cmds)
        if '_xa' in body:
            new_body = 'if (xa = 1) then ' + ('(' if self.__visit_properties else '') + body.format(ag='xa').replace('_xa_tx', '_1_nx').replace('_xa', '_1') + (')' if self.__visit_properties else '')
            for ag in range(2, self.__A+1):
                if not self.__visit_properties:
                    if ag == self.__A:
                        new_body += ' else '
                    else:
                        new_body += f' elsif (xa = {ag}) then '
                    new_body += body.format(ag='xa').replace('_xa_tx', f'_{ag}_nx').replace('_xa', f'_{ag}')
                else:
                    if ag == self.__A:
                        new_body += ' else '
                    else:
                        new_body += f' else if (xa = {ag}) then '
                    new_body += '(' + body.format(ag='xa').replace('_xa_tx', f'_{ag}_nx').replace('_xa', f'_{ag}') + ')'
            if not self.__visit_properties:
                body = new_body + ' fi'
            else:
                body = new_body
        body = add_to_body + '\n' + body
        if self.__prefix == 'constructor':
            for (g, ty) in self.__globals:
                if ty == 'bool':
                    self.__initial_const_globals[g.text] = 'false'
                # elif ty == ('MapAddr', 'int'):
                #     for i in range(1, self.__A + 1):
                #         self.__initial_const_globals[f'{g.text}_{i}'] = 0
                else:
                    self.__initial_const_globals[g.text] = 0
            # for (g, ty) in self.__globals:
            #     if g.text not in self.__globals and g.text
            #     if self.__globals_index[g.text] == 0:
            #         # self.__globals_index[g.text] = 1
            #         if ty == 'int': 
            #             self.__initial_const_globals[g.text] = 0
            #         elif ty == 'Address' or ty == 'Hash' or ty == 'Secret':
            #             self.__initial_const_globals[g.text] = 0# to be updated to modify self.__initial_const_globals[g.text] = ?
            #         elif ty == 'bool':
            #             self.__initial_const_globals[g.text] = 'false' # to be updated to modify self.__initial_const_globals[g.text] = ?
            #         elif ty == 'String':
            #             self.__initial_const_globals[g.text] = 0 # to be updated to modify self.__initial_const_globals[g.text] = ?
            #         else:
            #             self.__initial_const_globals[g.text] = 0 # to be updated to modify self.__initial_const_globals[g.text] = ?
        self.__proc_args[self.__prefix] = args
        
        if not self.__visit_properties:
            skip = f'\n\tw = {self.__t_curr_w};'
            skip += '\n\t' + '\n\t'.join([f'aw_{i} = {self.__t_curr_a[i]};' for i in range(1, self.__A+1)])
            skip += '\n\t' + '\n\t'.join([g.text + ' = ' + (f'(starting_{g.text} -> pre {g.text});' if self.__globals_index[g.text]+self.__globals_modifier < 0 else g.text + '_'+str(self.__globals_index[g.text]+self.__globals_modifier))+';' for (g, ty) in self.__globals if ty != ('MapAddr', 'int') and g.text != 'err']) if self.__globals else ''        
            skip += '\n\t' + '\n\t'.join([g.text + f'_{ag}' + ' = ' + (f'(starting_{g.text}_{ag} -> pre {g.text}_{ag});' if self.__globals_index[g.text]+self.__globals_modifier < 0 else g.text + '_' + str(ag) + '_'+str(self.__globals_index[g.text]+self.__globals_modifier))+';' for ag in range(1, self.__A+1) for (g, ty) in self.__globals if ty == ('MapAddr', 'int')]) if self.__globals else ''        
            # skip += '\n\t' + ('contract_not_constructed = false;' if self.__prefix == 'constructor' else 'contract_not_constructed = (true -> pre contract_not_constructed);')
            # body += skip
            # same = '\n\tcontract_not_constructed = true;' if self.__prefix == 'constructor' else '\n\tcontract_not_constructed = (true -> pre contract_not_constructed);'
            same = f'\n\tw = (starting_w -> pre w);'
            same += '\n\t' + '\n\t'.join([f'aw_{i} = (starting_aw_{i} -> pre aw_{i});' for i in range(1, self.__A+1)])
            same += '\n\t' + '\n\t'.join([g.text + ' = ' + f'(starting_{g.text} -> pre {g.text});' for (g, ty) in self.__globals if ty != ('MapAddr', 'int') and g.text != 'err']) if self.__globals else ''
            same += '\n\t' + '\n\t'.join([g.text + f'_{ag}' + ' = ' + f'(starting_{g.text}_{ag} -> pre {g.text}_{ag});' for ag in range(1, self.__A+1) for (g, ty) in self.__globals if ty == ('MapAddr', 'int')]) if self.__globals else ''
        else:
            skip = f' \n\tw_nx = {self.__t_curr_w}'
            skip += ' and \n\t' + '\n\t and '.join([f'aw_{i}_nx = {self.__t_curr_a[i]}' for i in range(1, self.__A+1)])
            aux = '\n\t and '.join([g.text + '_nx = ' + (f'{g.text}' if self.__globals_index[g.text]+self.__globals_modifier < 0 else g.text + '_'+str(self.__globals_index[g.text]+self.__globals_modifier))+'_nx' for (g, ty) in self.__globals if ty != ('MapAddr', 'int') and g.text != 'err']) if self.__globals else ''        
            skip += ' and \n\t' + (aux if aux else 'true')
            aux = '\n\t and '.join([g.text + '_' + str(ag) + '_nx = ' + (f'{g.text}_{ag}' if self.__globals_index[g.text]+self.__globals_modifier < 0 else g.text + '_' + str(ag) +'_nx' + '_' + str(self.__globals_index[g.text]+self.__globals_modifier)) for ag in range(1, self.__A+1) for (g, ty) in self.__globals if ty == ('MapAddr', 'int')]) if self.__globals else ''        
            skip += ' and \n\t' + (aux if aux else 'true')
            # if body.replace('skip', '').replace('\n', '').replace(' ', '').replace('and', ''):
            #     skip = ' and' + skip
            # body += skip
            same = f'\n\tw_nx = w'
            same += ' and \n\t' + '\n\t and '.join([f'aw_{i}_nx = aw_{i}' for i in range(1, self.__A+1)])
            aux = '\n\t and '.join([g.text + '_nx = ' + f'{g.text}' for (g, ty) in self.__globals if ty != ('MapAddr', 'int') and g.text != 'err']) if self.__globals else ''
            same += ' and \n\t' + (aux if aux else 'true')
            aux = '\n\t and '.join([g.text + '_' + str(ag) + '_nx = ' + f'{g.text}_{ag}' for ag in range(1, self.__A+1) for (g, ty) in self.__globals if ty == ('MapAddr', 'int')]) if self.__globals else ''
            same += ' and \n\t' + (aux if aux else 'true')
        
        err = ('err_'+str(self.__globals_index['err']+self.__globals_modifier)) if (self.__globals_index['err']+self.__globals_modifier)>=0 else 'false'
        if self.__visit_properties:
            if body.replace(' ', '').endswith('and'):
                self.__functions_prop[self.__prefix] = f'{body} if ({err}_nx) then \n{same} else {skip}\n'
            else:
                self.__functions_prop[self.__prefix] = f'{body} and if ({err}_nx) then \n{same} else {skip}\n'
        else:
            same += '\n\tcontract_not_constructed = true;' if self.__prefix == 'constructor' else '\n\tcontract_not_constructed = (true -> pre contract_not_constructed);'
            skip += '\n\t' + ('contract_not_constructed = false;' if self.__prefix == 'constructor' else 'contract_not_constructed = (true -> pre contract_not_constructed);')
            self.__functions[self.__prefix] = f'{body} if ({err}) then {same} else {skip}\nfi'

        # if self.__requires:
        #     req = ' and '.join(self.__requires)
        #     if self.__visit_properties:
        #         self.__functions_prop[self.__prefix] = f'if ({req}) then \n{body} \nelse {same}\n'
        #     else:
        #         self.__functions[self.__prefix] = f'if ({req}) then \n{body} \nelse {same}\nfi'
        # else:
        #     if self.__visit_properties:
        #         self.__functions_prop[self.__prefix] = body
        #     else:
        #         self.__functions[self.__prefix] = body
        


    # Visit a parse tree produced by TxScriptParser#argsExpr.
    def visitArgsExpr(self, ctx:TxScriptParser.ArgsExprContext):
        args = set()
        for arg in ctx.argExpr():
            if arg.var.text in self.__not_valid_names:
                raise Exception(f'{arg.var.text} is not a valid name for a function\'s argument, please choose a different name')
            if arg.ty.text != 'hash':
                args.add(self.__prefix + '_' + arg.var.text)
            if arg.var.text in self.__args_map:
                pref = self.__prefix.replace('_func', '')
                if not self.__visit_properties:
                    raise Exception(f'The argument named {arg.var.text} in {pref} function is not valid (another function has already an argument called {arg.var.text})')
            self.__args_map[arg.var.text] = (self.__prefix + '_' + arg.var.text, arg.ty.text)
        return args


    # Visit a parse tree produced by TxScriptParser#arg.
    def visitArg(self, ctx:TxScriptParser.ArgContext):
        return self.visitChildren(ctx)


    def send(self, sender, amount, negative=False):
        if not negative:
            op1 = '-'
            op2 = '+'
        else:
            op1 = '+'
            op2 = '-'
        # [ for i in range(1, self.__A+1) ]
        res = f'{self.__t_new_w} = {self.__t_curr_w} {op1} {amount}'
        if self.__visit_properties:
            res += ' and\n'
        else:
            res += ';\n'
        for ag in range(1, self.__A+1):
            if ag != 1:
                res += 'els'
            if ag == self.__A:
                res += 'e\n'
            else:
                res += f'if ({sender} = {ag})'
                res += ' then\n'
            for ag1 in range(1, self.__A+1):
                if ag == ag1:
                    res += f'\t{self.__t_new_a[ag1]} = {self.__t_curr_a[ag1]} {op2} {amount}'
                else:
                    res += f'\t{self.__t_new_a[ag1]} = {self.__t_curr_a[ag1]}'
                if self.__visit_properties:
                    if ag1 != self.__A:
                        res += ' and\n'
                    else:
                        res += '\n'
                else:
                    res += ';\n'
        if not self.__visit_properties: res += 'fi\n'
        return res

    # Visit a parse tree produced by TxScriptParser#sendCmd.
    def visitSendCmd(self, ctx:TxScriptParser.SendCmdContext):
        sender = self.visit(ctx.sender)
        self.__nesting_w += 1
        self.__nesting_aw += 1

        left = self.visit(ctx.amount)
        
        # for el in self.__prop_nested_i:
        #     if el in left:
        #         send_chk = f'And([Or(j != {el}, '+f'{left} >= 0) for j in range(A+1)])'.replace(el, 'j')
        #         break
        # else:
        send_chk = left + ' >= 0' + ' and '
        if self.__visit_properties:
            send_chk += left + ' <= ' + 'w'
        else:
            send_chk += left + ' <= ' + '(starting_w -> pre w)'
        # for el in self.__prop_nested_i:
        #     if el in left:
        #         send = f'And([Or(j != {el}, '+'send({sender}, {amount}, {t_curr_w}, {t_new_w}, {t_curr_a}, {t_new_a})) for j in range(A+1)])'
        #         break
        # else:
        #     el = None
        #     send = 'send({sender}, {amount}, {t_curr_w}, {t_new_w}, {t_curr_a}, {t_new_a})'
        if sender == 'sender_tx':
            sender = 'xa_tx'
        elif sender == 'sender' or sender == 'msg.sender' or sender == 'xa1':
            sender= 'xa'
        else:
            if sender in self.__globals_index:
                sender = 'starting_'+sender if self.__globals_index[sender]+self.__globals_modifier < 0 else sender + '_'+str(self.__globals_index[sender]+self.__globals_modifier)
            elif sender in self.__args_map:
                sender = self.__args_map[sender][0]
        # if el:
        #     res = res[:res.index('send')+4] + res[res.index('send')+4:].replace(el, 'j')
        
        res = self.send(sender, left)
        # self.__requires.add(send_chk)
        err = 'err' + '_' + str(self.__globals_index['err'])
        err1 = 'err' + '_' + str(self.__globals_index['err']-1) if self.__globals_index['err'] > 0 else 'false'
        self.__globals_index['err'] += 1
        if self.__visit_properties:
            err1 = err1+'_nx' if err1 != 'false' else err1
            res = f'(if (not({send_chk})) then {err}_nx=true else {err}_nx={err1}) \n and ' + res
        else:
            res = f'if (not({send_chk})) then {err}=true; else {err}={err1}; fi\n' + res
        
        if not self.__visit_properties:
            self.__t_curr_a = [f'aw_{i}_{self.__nesting_aw-1}' for i in range(self.__A+1)]
            self.__t_new_a = [f'aw_{i}_{self.__nesting_aw}' for i in range(self.__A+1)]
            self.__t_curr_w = 'w_' + str(self.__nesting_w-1)
            self.__t_new_w = 'w_' + str(self.__nesting_w)
        else:
            res = '(' + res + ')'
            self.__t_curr_a = [f'aw_{i}_{self.__nesting_aw-1}_nx' for i in range(self.__A+1)]
            self.__t_new_a = [f'aw_{i}_{self.__nesting_aw}_nx' for i in range(self.__A+1)]
            self.__t_curr_w = 'w_' + str(self.__nesting_w-1) + '_nx'
            self.__t_new_w = 'w_' + str(self.__nesting_w) + '_nx'
        self.__M += 1
        return res

    # Visit a parse tree produced by TxScriptParser#requireCmd.
    def visitRequireCmd(self, ctx:TxScriptParser.RequireCmdContext):
        err = 'err' + '_' + str(self.__globals_index['err'])
        err1 = 'err' + '_' + str(self.__globals_index['err']-1) if self.__globals_index['err'] > 0 else 'false'
        self.__globals_index['err'] += 1
        if self.__visit_properties:
            err1 = err1+'_nx' if err1 != 'false' else err1
            return f'(if (not({self.visit(ctx.child)})) then {err}_nx=true else {err}_nx={err1})\n'
        else:
            return f'if (not({self.visit(ctx.child)})) then {err}=true; else {err}={err1}; fi\n'
        # self.__requires.add(f'{self.visit(ctx.child)}')
        # return 'skip'

    # Visit a parse tree produced by TxScriptParser#skipCmd.
    def visitSkipCmd(self, ctx:TxScriptParser.SkipCmdContext):
        return 'skip'
        # return 'next_state_tx({t_curr_a}, awNext, {t_curr_w}, wNext{global_args_next_state_tx})'.format(
        #     t_curr_a=self.__t_curr_a, 
        #     t_curr_w=self.__t_curr_w, 
        #     global_args_next_state_tx = (', ' + ', '.join([(g.text + 'Now' if self.__globals_index[g.text]+self.__globals_modifier < 0 else 't_'+g.text + '['+str(self.__globals_index[g.text]+self.__globals_modifier)+']')+', '+g.text+'Next' for (g, _) in self.__globals])) if self.__globals else ''
        # )


    # Visit a parse tree produced by TxScriptParser#groupCmd.
    def visitGroupCmd(self, ctx:TxScriptParser.GroupCmdContext):
        return self.visit(ctx.child)
    

    # Visit a parse tree produced by TxScriptParser#sha256Expr.
    def visitSha256Expr(self, ctx:TxScriptParser.Sha256ExprContext):
        self.visit(ctx.child)
        return 'xa1'


    # Visit a parse tree produced by TxScriptParser#payableExpr.
    def visitPayableExpr(self, ctx:TxScriptParser.PayableExprContext):
        return self.visit(ctx.child)


    # Visit a parse tree produced by TxScriptParser#lengthExpr.
    def visitLengthExpr(self, ctx:TxScriptParser.LengthExprContext):
        return self.visit(ctx.child)
    

    # Visit a parse tree produced by TxScriptParser#assignCmd.
    def visitAssignCmd(self, ctx:TxScriptParser.AssignCmdContext):
        left = ctx.var.text
        # self.__globals_modifier -= 1
        right = self.visit(ctx.child)
        # self.__globals_modifier += 1
        i = self.__globals_index[left]
        self.__globals_index[left] = i+1
        # if self.__prefix == 'constructor':
        #     for (g, ty) in self.__globals:
        #         if ty == 'bool':
        #             self.__initial_const_globals[left] = 'false'
        #         else:
        #             self.__initial_const_globals[left] = 0
        aux = 0
        while '[' in right[aux:] and ']' in right[aux:] and right[right.index('[', aux)+1:right.index(']', aux)].isnumeric():
            aux = right.index(']', aux) + 1
            if aux >= len(right): break
        if aux != -1 and aux < len(right) and '[' in right[aux:] and ']' in right[aux:]:
            index = right[right.index('[', aux)+1:right.index(']', aux)]
            right = right.replace(index, 'j')
            return f'And([Or(j!={str(index)}, t_{left}[{str(i)}] == {right}) for j in range(A+1)])' 
        else:
            return left+'_'+str(i) + ('_nx' if self.__visit_properties else '') + ' = ' + right + (';' if not self.__visit_properties else '')
    

    # Visit a parse tree produced by TxScriptParser#assignMapCmd.
    def visitAssignMapCmd(self, ctx:TxScriptParser.AssignMapCmdContext):
        left = ctx.var.text
        index = self.visit(ctx.index)
        self.__globals_modifier -= 1
        right = self.visit(ctx.child)#.replace(str(index), 'j')
        self.__globals_modifier += 1

        if left in self.__globals_index:
            index = f'{index}_{self.__globals_index[left]}'

        i = self.__globals_index[left]
        self.__globals_index[left] = i+1
        return f'{left}_{index} = {right}' + (';' if not self.__visit_properties else '')
        # prev_i = f'{left}Now' if i == 0 else f't_{left}[{str(i-1)}]'
        # return f'And(And([Or(j!={str(index)}, t_{left}[{str(i)}][j] == {right}) for j in range(A+1)]), And([Or(j=={str(index)}, t_{left}[{str(i)}][j] == {prev_i}[j]) for j in range(A+1)]))' 
        # return 'And('+ 'And(' + f'[t_{left}[{str(i)}][j] == {right} for j in range(A+1) if j == {str(index)}]' + ')' + ', ' + 'And(' + f'[t_{left}[{str(i)}][j] == {prev_i}[j] for j in range(A+1) if j != {str(index)}]' + ')' ')'
        # return 'And('+ 't_'+left+'['+str(i)+']'+'['+str(index)+']' + ' == ' + right + ', ' + 'And(' + f'[t_{left}[{str(i)}][j] == {prev_i}[j] for j in range(A+1) if j != {str(index)}]' + ')' ')'


    # Visit a parse tree produced by TxScriptParser#ifCmd.
    def visitIfCmd(self, ctx:TxScriptParser.IfCmdContext):
        cond = self.visit(ctx.condition)
        backup_globals = self.__globals_index.copy()
        backup_add = self.__add_last_cmd
        self.__add_last_cmd = False
        backup_nesting_w = self.__nesting_w
        backup__t_curr_a = self.__t_curr_a
        backup__t_curr_w = self.__t_curr_w
        ifcmd = self.visit(ctx.ifcmd)
        ifcmd = ifcmd.format(subs='true')
        # self.__globals_index = backup
        self.__add_last_cmd = backup_add
        levelling_else_cmds = []
        if self.__nesting_w > backup_nesting_w:
            levelling_else_cmds += [f'{self.__t_curr_w}={backup__t_curr_w}'] #+ (' and ' if self.__visit_properties else ';') # And([{if__t_curr_a}[j] == {self.__t_curr_a}[j] for j in range(A+1)])'
            for ag1 in range(1, self.__A+1):
                levelling_else_cmds += [f'{self.__t_curr_a[ag1]} = {backup__t_curr_a[ag1]}'] # + (' and ' if self.__visit_properties else ';')
            # if self.__visit_properties:
            #     levelling_else_cmds = levelling_else_cmds[:-5]
            # levelling_else_cmds += f', {backup__t_curr_w}=={self.__t_curr_w}, And([{backup__t_curr_a}[j] == {self.__t_curr_a}[j] for j in range(A+1)])'
        for g in self.__globals_index:
            for (gg,gt) in self.__globals:
                if gg.text == g:
                    break
            if gt == ('MapAddr', 'int'):
                if backup_globals[g] < self.__globals_index[g]:
                    for ag in range(1, self.__A+1):
                        tg_now = f'{g}_{backup_globals[g]}' if backup_globals[g] > 0 else f'starting_{g}_{ag}'
                        levelling_else_cmds += [f'{g}_{self.__globals_index[g]-1}_{ag} = {tg_now}_{ag}']
                    # levelling_else_cmds += f', t_{g}[{self.__globals_index[g]-1}]=={tg_now}'
            else:
                if backup_globals[g] < self.__globals_index[g]:
                    tg_now = f'{g}_{backup_globals[g]-1}' if backup_globals[g] > 0 else f'starting_{g}'
                    levelling_else_cmds += [f'{g}_{self.__globals_index[g]-1} = {tg_now}'] #+ (';' if not self.__visit_properties else '')
        if self.__visit_properties:
            levelling_else_cmds = ' and '.join(levelling_else_cmds)
            return f'(if {cond} then {ifcmd} else {levelling_else_cmds})'
        else:
            levelling_else_cmds = '; '.join(levelling_else_cmds) + ';'
            return f'if ({cond}) then {ifcmd} else {levelling_else_cmds} fi'
    

    # Visit a parse tree produced by TxScriptParser#ifelseCmd.
    def visitIfelseCmd(self, ctx:TxScriptParser.IfelseCmdContext):
        cond = self.visit(ctx.condition)
        # backup = self.__globals_index.copy()
        backup_add = self.__add_last_cmd
        self.__add_last_cmd = False
        backup__t_curr_a = self.__t_curr_a
        backup__t_new_a = self.__t_new_a
        backup__t_curr_w = self.__t_curr_w
        backup__t_new_w = self.__t_new_w
        backup_nesting_w = self.__nesting_w
        backup_nesting_aw = self.__nesting_aw
        backup_M = self.__M
        backup_global_index = copy.deepcopy(self.__globals_index)
        ifcmd = self.visit(ctx.ifcmd)
        if_backup_M = self.__M
        ifcmd = ifcmd.format(subs='true')
        # skip = 'next_state_tx({t_curr_a}, awNext, {t_curr_w}, wNext{global_args_next_state_tx})'.format(
        #     t_curr_a=self.__t_curr_a, 
        #     t_curr_w=self.__t_curr_w, 
        #     global_args_next_state_tx = (', ' + ', '.join([(g.text + 'Now' if self.__globals_index[g.text]+self.__globals_modifier < 0 else 't_'+g.text + '['+str(self.__globals_index[g.text]-1+self.__globals_modifier)+']')+', '+g.text+'Next' for (g, _) in self.__globals])) if self.__globals else ''
        # )
        if__t_curr_a = self.__t_curr_a
        if__t_new_a = self.__t_new_a
        if__t_curr_w = self.__t_curr_w
        if__t_new_w = self.__t_new_w
        if_nesting_w = self.__nesting_w
        if_nesting_aw = self.__nesting_aw
        if_globals_index = copy.deepcopy(self.__globals_index)
        self.__t_curr_a = backup__t_curr_a
        self.__t_new_a = backup__t_new_a
        self.__t_curr_w = backup__t_curr_w
        self.__t_new_w = backup__t_new_w
        self.__nesting_w = backup_nesting_w
        self.__nesting_aw = backup_nesting_aw
        self.__globals_index = backup_global_index
        self.__M = backup_M
        elsecmd = self.visit(ctx.elsecmd)
        elsecmd = elsecmd.format(subs='true')
        self.__M = max(self.__M, if_backup_M)
        # skip = 'next_state_tx({t_curr_a}, awNext, {t_curr_w}, wNext{global_args_next_state_tx})'.format(
        #     t_curr_a=self.__t_curr_a, 
        #     t_curr_w=self.__t_curr_w, 
        #     global_args_next_state_tx = (', ' + ', '.join([(g.text + 'Now' if self.__globals_index[g.text]+self.__globals_modifier < 0 else 't_'+g.text + '['+str(self.__globals_index[g.text]-1+self.__globals_modifier)+']')+', '+g.text+'Next' for (g, _) in self.__globals])) if self.__globals else ''
        # )
        levelling_if_cmds = []
        levelling_else_cmds = []
        if if_nesting_w > self.__nesting_w:
            levelling_else_cmds += [f'{if__t_curr_w}={self.__t_curr_w}'] # And([{if__t_curr_a}[j] == {self.__t_curr_a}[j] for j in range(A+1)])'
            for ag1 in range(1, self.__A+1):
                levelling_else_cmds += [f'{if__t_curr_a[ag1]} = {self.__t_curr_a[ag1]}']
            self.__t_curr_a = if__t_curr_a
            self.__t_new_a = if__t_new_a
            self.__t_curr_w = if__t_curr_w
            self.__t_new_w = if__t_new_w
            self.__nesting_w = if_nesting_w
            self.__nesting_aw = if_nesting_aw
        elif if_nesting_w < self.__nesting_w:
            levelling_if_cmds += [f'{self.__t_curr_w} = {if__t_curr_w}'] # And([{if__t_curr_a}[j] == {self.__t_curr_a}[j] for j in range(A+1)])'
            for ag1 in range(1, self.__A+1):
                levelling_if_cmds += [f'{self.__t_curr_a[ag1]} = {if__t_curr_a[ag1]}']
        for g in self.__globals_index:
            for (gg,gt) in self.__globals:
                if gg.text == g:
                    break 
            if gt == ('MapAddr', 'int'):
                if if_globals_index[g] > self.__globals_index[g]:
                    for ag in range(1, self.__A+1):
                        tg_now = f'{g}_{self.__globals_index[g]}_{ag}' if self.__globals_index[g] > 0 else f'starting_{g}'
                        # levelling_else_cmds += f', t_{g}[{if_globals_index[g]-1}]=={tg_now}'
                        levelling_else_cmds += [f'{g}_{if_globals_index[g]-1}_{ag} = {tg_now}']
                    self.__globals_index[g] = if_globals_index[g]
                elif if_globals_index[g] < self.__globals_index[g]:
                    for ag in range(1, self.__A+1):
                        tg_now = f'{g}_{if_globals_index[g]}_{ag}' if if_globals_index[g] > 0 else f'starting_{g}'
                        # levelling_if_cmds += f', {tg_now}==t_{g}[{self.__globals_index[g]-1}]'
                        levelling_if_cmds += [f'{tg_now}_{ag} = {g}[{self.__globals_index[g]-1}][j] for j in range(A+1)])']
            else:
                if if_globals_index[g] > self.__globals_index[g]:
                    tg_now = f'{g}_{self.__globals_index[g]}' if self.__globals_index[g] > 0 else f'starting_{g}'
                    levelling_else_cmds += [f'{g}_{if_globals_index[g]-1}={tg_now}']
                    self.__globals_index[g] = if_globals_index[g]
                elif if_globals_index[g] < self.__globals_index[g]:
                    tg_now = f'{g}_{if_globals_index[g]}' if if_globals_index[g] > 0 else f'starting_{g}'
                    levelling_if_cmds += [f'{g}_{self.__globals_index[g]-1}={tg_now}']
        self.__add_last_cmd = backup_add
        if self.__visit_properties:
            levelling_if_cmds = ' and '.join(levelling_if_cmds)
            levelling_else_cmds = ' and '.join(levelling_else_cmds)
        else:
            levelling_if_cmds = '; '.join(levelling_if_cmds) + ';' if levelling_if_cmds else ''
            levelling_else_cmds = '; '.join(levelling_else_cmds) + ';' if levelling_else_cmds else ''
        # self.__globals_index = backup
        ifcmd_aux = ifcmd.format(subs=levelling_if_cmds)
        if ifcmd_aux == ifcmd and levelling_if_cmds:
            ifcmd += (' and' if self.__visit_properties else '') + f' {levelling_if_cmds}'
        else:
            ifcmd = ifcmd_aux
        elsecmd_aux = elsecmd.format(subs=levelling_else_cmds)
        if elsecmd_aux == elsecmd and levelling_else_cmds:
            elsecmd += (' and' if self.__visit_properties else '') + f' {levelling_else_cmds}'
        else:
            elsecmd = elsecmd_aux

        if self.__visit_properties:
            return f'(if {cond} then {ifcmd} else {elsecmd})'
        else:
            return f'if ({cond}) then {ifcmd} else {elsecmd} fi'


    # Visit a parse tree produced by TxScriptParser#seqCmd.
    def visitSeqCmd(self, ctx:TxScriptParser.SeqCmdContext):
        seq1 = self.visit(ctx.seq1)
        seq2 = self.visit(ctx.seq2)
        if self.__visit_properties:
            return seq1 + ' and ' + seq2
        else:
            return seq1 + '\n' + seq2
        # aux = seq1.format(subs='And('+seq2+',{subs})')
        # if aux == seq1:
        #     return 'And(\n\t{seq1},\n\t{seq2})'.format(seq1=seq1, seq2=seq2)
        # else:
        #     return aux


    # Visit a parse tree produced by TxScriptParser#groupExpr.
    def visitGroupExpr(self, ctx:TxScriptParser.GroupExprContext):
        return self.visit(ctx.child)


    # Visit a parse tree produced by TxScriptParser#greaterEqExpr.
    def visitGreaterEqExpr(self, ctx:TxScriptParser.GreaterEqExprContext):
        left = self.visit(ctx.left)
        right = self.visit(ctx.right)
        # if not self.__visit_properties_body:
        for el in self.__prop_nested_i:
            if el in left or el in right:
                return f'And([Or(j != {el}, '+f'{left} >= {right}) for j in range(A+1)])'.replace(el, 'j')
        return left + '>=' + right
        # else:
        #     for el in self.__prop_nested_i:
        #         if el in left or el in right:
        #             return f'And([Or(j != {el}, '+f'{left} >= {right}) for j in range(A+1)])'.replace(el, 'j')        
        #     return f'Not({left} >= {right})'



    # Visit a parse tree produced by TxScriptParser#lessExpr.
    def visitLessExpr(self, ctx:TxScriptParser.LessExprContext):
        left = self.visit(ctx.left)
        right = self.visit(ctx.right)
        # if not self.__visit_properties_body:
        for el in self.__prop_nested_i:
            if el in left or el in right:
                return f'And([Or(j != {el}, '+f'{left} < {right}) for j in range(A+1)])'.replace(el, 'j')
        return left + '<' + right
        # else:
        #     for el in self.__prop_nested_i:
        #         if el in left or el in right:
        #             return f'And([Or(j != {el}, '+f'Not({left} < {right})) for j in range(A+1)])'.replace(el, 'j')        
        #     return f'Not({left} < {right})'


    # Visit a parse tree produced by TxScriptParser#neqExpr.
    def visitNeqExpr(self, ctx:TxScriptParser.NeqExprContext):
        left = self.visit(ctx.left)
        right = self.visit(ctx.right)
        return 'not(' + left + '=' + right + ')'


    # # Visit a parse tree produced by TxScriptParser#variableExpr.
    # def visitVariableExpr(self, ctx:TxScriptParser.VariableExprContext):
    #     return self.visitChildren(ctx)


    # Visit a parse tree produced by TxScriptParser#greaterExpr.
    def visitGreaterExpr(self, ctx:TxScriptParser.GreaterExprContext):
        left = self.visit(ctx.left)
        right = self.visit(ctx.right)
        # if not self.__visit_properties_body:
        for el in self.__prop_nested_i:
            if el in left or el in right:
                return f'And([Or(j != {el}, '+f'{left} > {right}) for j in range(A+1)])'.replace(el, 'j')
        return left + '>' + right
        # else:
        #     for el in self.__prop_nested_i:
        #         if el in left or el in right:
        #             return f'And([Or(j != {el}, '+f'Not({left} > {right})) for j in range(A+1)])'.replace(el, 'j')        
        #     return f'Not({left} > {right})'


    # Visit a parse tree produced by TxScriptParser#eqExpr.
    def visitEqExpr(self, ctx:TxScriptParser.EqExprContext):
        left = self.visit(ctx.left)
        right = self.visit(ctx.right)
        if left == 'tx_sender':
            self.__tx_sender = right
            return 'true'
        if right == 'tx_sender':
            self.__tx_sender = left
            return 'true'
        # if self.__visit_properties:
        #     return f'{left} = {right}'    
        # else:
        return f'{left} = {right}'


    # Visit a parse tree produced by TxScriptParser#notExpr.
    def visitNotExpr(self, ctx:TxScriptParser.NotExprContext):
        return 'not('+self.visit(ctx.child)+')'


    # Visit a parse tree produced by TxScriptParser#sumSubExpr.
    def visitSumSubExpr(self, ctx:TxScriptParser.SumSubExprContext):
        left = self.visit(ctx.left)
        right = self.visit(ctx.right)
        if not self.__visit_properties:
            post = 'Now'
        else:
            post = ''
        if left in self.__globals_index:
            if self.__globals_index[left]+self.__globals_modifier < 0:
                left = left + post
            else:
                left = 't_'+left + '['+str(self.__globals_index[left]+self.__globals_modifier)+']'
        if right in self.__globals_index:
            if self.__globals_index[right]+self.__globals_modifier < 0:
                right = right + post
            else:
                right = 't_'+right + '['+str(self.__globals_index[right]+self.__globals_modifier)+']'
        return '(' + left + ctx.op.text + right + ')'


    # Visit a parse tree produced by TxScriptParser#lessEqExpr.
    def visitLessEqExpr(self, ctx:TxScriptParser.LessEqExprContext):
        left = self.visit(ctx.left)
        right = self.visit(ctx.right)
        # if not self.__visit_properties_body:
        for el in self.__prop_nested_i:
            if el in left or el in right:
                return f'And([Or(j != {el}, '+f'{left} <= {right}) for j in range(A+1)])'.replace(el, 'j')
        return left + '<=' + right
        # else:
        #     for el in self.__prop_nested_i:
        #         if el in left or el in right:
        #             return f'And([Or(j != {el}, '+f'Not({left} <= {right})) for j in range(A+1)])'.replace(el, 'j')        
        #     return f'Not({left} <= {right})'


    # Visit a parse tree produced by TxScriptParser#constExpr.
    def visitConstExpr(self, ctx:TxScriptParser.ConstExprContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TxScriptParser#multDivModExpr.
    def visitMultDivModExpr(self, ctx:TxScriptParser.MultDivModExprContext):
        left = self.visit(ctx.left)
        right = self.visit(ctx.right)
        if left in self.__globals_index:
            if self.__globals_index[left]+self.__globals_modifier < 0:
                left = left + 'Now'
            else:
                left = 't_'+left + '['+str(self.__globals_index[left]+self.__globals_modifier)+']'
        if right in self.__globals_index:
            if self.__globals_index[right]+self.__globals_modifier < 0:
                right = right + 'Now'
            else:
                right = 't_'+right + '['+str(self.__globals_index[right]+self.__globals_modifier)+']'
        res = '(' + left + ctx.op.text + right + ')'
        #  left out for now, it would require to keep track of the division and propagate their handling in the assign command
        # if ctx.op.text == '/':
        #     res = 'If(\n\tNot(' + right + ' != 0), \n\t\tnext_state_tx(awNow, awNext, wNow, wNext'+((', ' + ', '.join([g.text+'Now, '+g.text+'Next' for (g, _) in self.__globals])) if self.__globals else '')+'), And(' + res + ', {subs}))'        
        return res


    # Visit a parse tree produced by TxScriptParser#andExpr.
    def visitAndExpr(self, ctx:TxScriptParser.AndExprContext):
        return '(' + self.visit(ctx.left) + ' and ' + self.visit(ctx.right) + ')'
    

    # Visit a parse tree produced by TxScriptParser#orExpr.
    def visitOrExpr(self, ctx:TxScriptParser.OrExprContext):
        return '(' + self.visit(ctx.left) + ' or ' + self.visit(ctx.right) + ')'


    # # Visit a parse tree produced by TxScriptParser#orWithdrawExpr.
    # def visitOrWithdrawExpr(self, ctx:TxScriptParser.OrWithdrawExprContext):
    #     return f'Or({self.visit(ctx.left)},{self.visit(ctx.right)})'


    # # Visit a parse tree produced by TxScriptParser#andWithdrawExpr.
    # def visitAndWithdrawExpr(self, ctx:TxScriptParser.AndWithdrawExprContext):
    #     return f'And({self.visit(ctx.left)},{self.visit(ctx.right)})'


    # # Visit a parse tree produced by TxScriptParser#baseWithdrawExpr.
    # def visitBaseWithdrawExpr(self, ctx:TxScriptParser.BaseWithdrawExprContext):
    #     index = self.visit(ctx.ag)
    #     arr_name = 'w'
    #     res = f'Not(w_q <= {arr_name}[{index}]-({self.visit(ctx.body)}))'
    #     if '[i]' in index:
    #         res_with_j = res.replace(f"{arr_name}[{index}]", f"{arr_name}[j]")
    #         return f"And([Or(j != {index}, {res_with_j}) for j in range(A+1)])"
    #     else:
    #         return res


    # Visit a parse tree produced by TxScriptParser#qslf.
    def visitQslf(self, ctx:TxScriptParser.QslfContext):
        for k in self.__globals_index:
            self.__globals_index[k] = 0
        user_is_legit = ' or '.join([f'xa_tx = {i}' for i in range(1, self.__A+1)])
        ntrans = int(ctx.nTrans.text)
        transition_vars = ''
        transition_vars += 'f_tx: functions; ' + ' '.join(['{a}_tx: {t};'.format(a=self.__args_map[a][0], t=self.__args_map[a][1]).replace('address', 'int') for a in self.__args_map if self.__args_map[a][1] != 'hash'])
        transition_vars += ' xn_tx: int;'
        for i in range(2, ntrans+1):
            transition_vars += f'f_tx{i}: functions; ' + ' '.join(['{a}_tx{i}: {t};'.format(i=i, a=self.__args_map[a][0], t=self.__args_map[a][1]) for a in self.__args_map if self.__args_map[a][1] != 'hash'])
            transition_vars += f' xn_tx{i}: int;'
        contract_globals = []
        contract_globals += ['w_nx: int;']
        contract_globals += [f'w_{i}_nx: int;' for i in range(self.__max_nesting + 1)]
        contract_globals += [f'aw_{ag}_nx: int;' for ag in range(1, self.__A+1)]
        contract_globals += [f'aw_{ag}_{i}_nx: int;' for ag in range(1, self.__A+1) for i in range(self.__max_nesting + 1)]
        for (g_var,g_type) in self.__globals:
            if g_type == ('MapAddr', 'int'):
                contract_globals += [f'{g_var.text}_{ag}_nx : int;' for ag in range(1, self.__A+1)]
                contract_globals += [f'{g_var.text}_{ag}_nx_{i} : int;' for i in range(self.__globals_index_max[g_var.text]) for ag in range(1, self.__A+1)] 
            else:
                if g_type == 'Address' or g_type == 'Hash' or g_type == 'Secret':
                    g_type = 'int'
                contract_globals += [f'{g_var.text}_nx : {g_type};']
                contract_globals += [f'{g_var.text}_{i}_nx : {g_type};' for i in range(self.__globals_index_max[g_var.text] + (1 if g_var.text != 'err' else 2))]  
        for j in range(2, ntrans+1):
            contract_globals += [f'w_nx{j}: int;']
            contract_globals += [f'w_{i}_nx{j}: int;' for i in range(self.__max_nesting + 1)]
            contract_globals += [f'aw_{ag}_nx{j}: int;' for ag in range(1, self.__A+1)]
            contract_globals += [f'aw_{ag}_{i}_nx{j}: int;' for ag in range(1, self.__A+1) for i in range(self.__max_nesting + 1)]
            for (g_var,g_type) in self.__globals:
                if g_type == ('MapAddr', 'int'):
                    contract_globals += [f'{g_var.text}_{ag}_nx{j} : int;' for ag in range(1, self.__A+1)]
                    contract_globals += [f'{g_var.text}_{ag}_{i}_nx{j} : int;' for i in range(self.__globals_index_max[g_var.text]) for ag in range(1, self.__A+1)]
                else:
                    if g_type == 'Address' or g_type == 'Hash' or g_type == 'Secret':
                        g_type = 'int'
                    contract_globals += [f'{g_var.text}_nx{j} : {g_type};']
                    contract_globals += [f'{g_var.text}_{i}_nx{j} : {g_type};' for i in range(self.__globals_index_max[g_var.text] + (1 if g_var.text != 'err' else 2))]
            
        next_state_vars = ' '.join(contract_globals)
        implication = 'not(' + self.visit(ctx.where) + ')'
        implication = implication.replace('_nx', '')
        # self.__visit_properties_body = True
        body = self.visit(ctx.body)
        # self.__visit_properties_body = False
        if ntrans >= 2:
            body = body.replace('_nx', '_nx2')
        condition = ' and '.join([f'(not(xa_tx = {ag}) or ' + body.format(ag = ag) + ')' for ag in range(1, self.__A+1)])
        self.visit(self.__ctx)
        contract = ''
        n_tabs = 0
        keys = list(self.__proc_args.keys())
        keys.append('dummy')
        if 'constructor' in keys: keys.remove('constructor')
        if keys:
            for p in keys[:-1]:
                if p == keys[0]:
                    cmd = 'if'
                else:
                    cmd = 'else if'
                contract += '\t'*n_tabs + cmd + ' f_tx = ' + p + ' then\n'
                n_tabs += 1
                contract += f'\t{self.__functions_prop[p]}\n'
            n_tabs += 1
            contract += 'else'
            same = f'\n\tw_nx = w '
            same += ' and \n\t' + '\n\tand '.join([f'aw_{i}_nx = aw_{i}' for i in range(1, self.__A+1)])
            # same += ' and \n\t' + '\n\tand '.join([g.text + '_nx = ' + f'{g.text}' for (g, _) in self.__globals]) if self.__globals else ''
            aux = '\n\t and '.join([g.text + '_nx = ' + f'{g.text}' for (g, ty) in self.__globals if ty != ('MapAddr', 'int')]) if self.__globals else ''
            same += ' and \n\t' + (aux if aux else 'true')
            aux = '\n\t and '.join([g.text + '_' + str(ag) + '_nx = ' + f'{g.text}_{ag}' for ag in range(1, self.__A+1) for (g, ty) in self.__globals if ty == ('MapAddr', 'int')]) if self.__globals else ''
            same += ' and \n\t' + (aux if aux else 'true')
            contract += f'{same}\n'
        contracts = [contract]
        nx = '_nx'
        nx1 = '_nx2'
        for i in range(2, ntrans+1):
            aux = contract
            aux = aux.replace('_nx', nx1)
            # List of (pattern substring, replacement string) pairs
            substitutions = [
                ('\nw ', f'\nw{nx} '),
                (' w\n', f' w{nx}\n'),
                (' w ', f' w{nx} '),
                (' w)', f' w{nx})'),
                ('(w ', f'(w{nx} ')
            ]
            # Apply each substitution using a regex with a negative lookahead
            for substring, replacement in substitutions:
                pattern = re.escape(substring) + r'(?!_)'
                aux = re.sub(pattern, replacement, aux)
            for k in self.__globals_index:
                pattern = r'(?<!starting_)' + re.escape(k) + r'(?!_)'
                aux = re.sub(pattern, f'{k}{nx}', aux)
            for k in range(0, 100):
                k = '_' + str(k)
                pattern = r'(?<!starting_)' + re.escape(k) + r'(?!_)'
                aux = re.sub(pattern, f'{k}{nx}', aux)
            for j in range(1, self.__A+1):
                pattern = re.escape(f'aw_{j}') + r'(?!_)'
                aux = re.sub(pattern, f'aw_{j}{nx}', aux)
            aux = aux.replace('_tx', f'_tx{i}')
            aux = aux.replace(f'xa_tx{i}', 'xa_tx')
            contracts.append(aux)
            nx = f'_nx{i}'
            nx1 = f'_nx{i+1}'
        contracts = ' and '.join(f'({c})' for c in contracts)
        pi = f'''--%PROPERTY 
forall (xa_tx: int;)
    (not ({user_is_legit}) or {implication} or (contract_not_constructed)) /* user is legit*/
    or
    exists (
            {transition_vars}  /* Transition vars */
            {next_state_vars} /* Next state vars */
    )
    (
        (   /* condition */
            {condition}
        )
        and
        (
        {contracts}
        )
    );
'''
        print(pi)
        return pi
    

    # Visit a parse tree produced by TxScriptParser#numberConstant.
    def visitNumberConstant(self, ctx:TxScriptParser.NumberConstantContext):
        return ctx.v.text
    

    # Visit a parse tree produced by TxScriptParser#mapExpr.
    def visitMapExpr(self, ctx:TxScriptParser.MapExprContext):
        index = self.visit(ctx.index)
        if not self.__visit_properties:
            if ctx.mapVar.text in self.__globals_index:
                self.__prop_nested_i.add(index)
                if self.__globals_index[ctx.mapVar.text] + self.__globals_modifier < 0:
                    return f'(starting_{ctx.mapVar.text}_{index} -> pre {ctx.mapVar.text}_{index})'
                else:
                    return f'{ctx.mapVar.text}_{index}_' + str(self.__globals_index[ctx.mapVar.text])
            return f'{ctx.mapVar.text}_{index}' #ctx.mapVar.text + '[' + index + ']'
        else:
            if 'app_tx_st' in ctx.mapVar.text:
                i = '_nx'
                name = ctx.mapVar.text.replace('app_tx_', '')
            else:
                name = ctx.mapVar.text
                i = ''
            if 'balance' in name:
                ag = index.replace('_q', '')
                if ag == 'xa':
                    self.__prop_nested_i.add(ag+'_q')#(ag+'[i]')
                    return 'aw_{ag}' + i #f'aw{i}[{ag}[i]]'
                else:
                    self.__prop_nested_i.add(ag)#(ag+'[i]')
                    return 'aw_{ag}' + i #f'aw{i}[{ag}[i]]'
            if name.replace('st.','') in self.__args_map:
                return self.__args_map[ctx.v.text][0]  
            if name.replace('st.','') in self.__globals_index:  
                ag = index.replace('_q', '')
                if ag == 'xa':
                    self.__prop_nested_i.add(ag+'_q')#(ag+'[i]')
                    return name.replace('st.','') + f'_{ag}' + i
                else:
                    # if '[i]' not in ag:
                    #     ag = ag+'[i]'
                    self.__prop_nested_i.add(ag)#(ag+'[i]')
                    return name.replace('st.','') + '_{ag}' + i
            return name.replace('st.', '')


    # Visit a parse tree produced by TxScriptParser#strConstant.
    def visitStrConstant(self, ctx:TxScriptParser.StrConstantContext):
        if not self.__visit_properties:
            if ctx.v.text == 'balance':
                return self.__t_curr_w
            if ctx.v.text == 'block.number':
                return 'block_num'
            if ctx.v.text == 'msg.value' or ctx.v.text == 'value':
                return 'xn'
            if ctx.v.text == 'msg.sender' or ctx.v.text == 'sender':
                return 'xa'
            if ctx.v.text in self.__args_map:
                if self.__args_map[ctx.v.text][1] == 'hash':
                    return 'xa'
                else:
                    return self.__args_map[ctx.v.text][0]
            if ctx.v.text in self.__globals_index:
                if self.__globals_index[ctx.v.text]+self.__globals_modifier < 0:
                    return f'(starting_{ctx.v.text} -> pre {ctx.v.text})' #ctx.v.text + 'Now'
                else:
                    return ctx.v.text + '_' + str(self.__globals_index[ctx.v.text]+self.__globals_modifier)
            return ctx.v.text
        else:
            if 'app_tx_st' in ctx.v.text:
                name = ctx.v.text.replace('app_tx_st', 'st')
                i = '_nx'
            else:
                name = ctx.v.text
                i = ''
            if 'balance' in name and '[' in name and ']' in name:
                ag = name[name.index('[')+1:name.index(']')]
                if ag == 'xa': # aw_q0[xa_q] == (aw[i][xa_q]+w[i])    aw_1_nx = aw_1 + w
                    self.__prop_nested_i.add(ag+'_q')#(ag+'[i]')
                    return 'aw_{ag}' + i #f'aw{i}[{ag}[i]]'
                else:
                    self.__prop_nested_i.add(ag+'[i]')#(ag+'[i]')
                    return 'aw_{ag}' + i #f'aw{i}[{ag}[i]]'
            if '.balance' in name and name != 'st.balance':
                ag = name[:name.index('.balance')].replace('st.', '')
                if ag == 'xa':
                    self.__prop_nested_i.add(ag+'_q')#(ag+'[i]')
                    return 'aw_{ag}' + i #f'aw{i}[{ag}[i]]'
                else:
                    self.__prop_nested_i.add(ag+'[i]')#(ag+'[i]')
                    return f'aw_{ag}' + i #f'aw{i}[{ag}[i]]'
            if 'balance' in name:
                return 'w' + i
            if 'block.number' in name:
                return 'block_num' + i
            if 'msg.value' in name:
                return 'xn_tx'
                # return 'xn_'+f'{self.__n_transactions-1-(self.__n_transactions-self.__pi)}_tx'
            # if 'tx.msg.sender' in name:
            #     return 'tx_sender'
            if ctx.v.text == 'msg.sender' or ctx.v.text == 'sender' or ctx.v.text == 'xa':
                return 'xa_tx'
            if name.replace('st.','') in self.__args_map:
                if self.__args_map[name][1] == 'hash':
                    return 'xa_tx'
                else:
                    return self.__args_map[name][0] + '_tx' 
            if name.replace('st.','') in self.__globals_index:              
                # return name.replace('st.','') + i
                if self.__globals_index[name.replace('st.','')]+self.__globals_modifier < 0:
                    return name.replace('st.','')
                else:
                    return name.replace('st.', '') + '_' + str(self.__globals_index[name.replace('st.','')]+self.__globals_modifier) + '_nx'
            if name == 'sender':
                return name + '_tx'
            return name.replace('st.', '')


    # Visit a parse tree produced by TxScriptParser#trueConstant.
    def visitTrueConstant(self, ctx:TxScriptParser.TrueConstantContext):
        return 'true'


    # Visit a parse tree produced by TxScriptParser#falseConstant.
    def visitFalseConstant(self, ctx:TxScriptParser.FalseConstantContext):
        return 'false'
    
