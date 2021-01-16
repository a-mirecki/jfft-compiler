import copy
import ply.lex as lex
import ply.yacc as yacc
import sys
from exceptions import *
import traceback

memoryInd, bufferId = 0, 0
instructions, initialized, declared, iterators, indexes, uiterators, arrays, usages, memory, instructionBuffer, = [], [], [], [], [], [], {}, {}, {}, {}
rtol = ["a", "b", "c", "d", "e", "f"]

def clear_ins_buffer(*args):
    for arg in args:
        instructionBuffer[arg] = []

def add_commands(commands=None, setBuffer=-1):
    global instructions, instructionBuffer, bufferId
    bufferId = setBuffer if setBuffer != -1 else bufferId

    if bufferId != 0:
        if bufferId not in instructionBuffer:
            instructionBuffer[bufferId] = []
        instructionBuffer[bufferId] += commands if commands is not None else []
    else:
        instructions += commands if commands is not None else []

def declare_variable(a):
    global memory, memoryInd
    if a == 999:
        raise Exception()
    if isinstance(a,tuple):
        memory[a[1]] = memoryInd
        memoryInd += (arrays[a[1]][1] - arrays[a[1]][0] + 1) if isinstance(a, tuple) else 1
    else:
        memory[a] = memoryInd
        memoryInd += 1

def set_mem_reg(addr, bid):
    set_register(0, addr, bid)

def reg_to_mem(reg, addr, bid):
    set_mem_reg(addr, bid)
    add_commands([f"STORE {rtol[reg]} a"], bid)

def mem_to_reg(reg, addr, bid):
    set_mem_reg(addr, bid)
    add_commands([f"LOAD {rtol[reg]} a"], bid)

def set_register(reg, val, bid):
    add_commands([f"RESET {rtol[reg]}"], bid)
    binn = str(bin(val).replace('0b', ''))
    for ind, dig in enumerate(binn):
        if dig == '1':
            add_commands([f"INC {rtol[reg]}"], bid)
        if ind < len(binn) - 1:
            add_commands([f"SHL {rtol[reg]}"], bid)

def _for(iterator, _from, _to, reverse, bid):
    global memoryInd, instructionBuffer
    if isinstance(_from, int) and isinstance(_to, int):
        _from, _to = (0, _to-_from) if not reverse and _to >= _from and iterator not in uiterators else (_from-_to, 0) if reverse and _from >= _to and iterator not in uiterators else (_from, _to)
    evaluate_operation(_from, _to, 0, bid-1, performOperation=False)
    memory[f"{iterator}_e"] = memoryInd
    memoryInd += 1
    reg_to_mem(1, memory[f"{iterator}"], bid-1)
    reg_to_mem(2, memory[f"{iterator}_e"], bid-1)
    insBufBack1 = copy.deepcopy(instructionBuffer[bid+1]) if bid+1 in instructionBuffer else []
    insBufBack2 = copy.deepcopy(instructionBuffer[bid+2]) if bid+2 in instructionBuffer else []
    clear_ins_buffer(bid+1, bid+2)
    mem_to_reg(1,memory[f"{iterator}"], bid+1)
    mem_to_reg(2,memory[f"{iterator}_e"], bid+1)
    reg_to_mem(1, memory[f"{iterator}"], bid+2)
    if reverse:
        add_commands(
            [f"JZERO b {len(instructionBuffer[bid + 2]) + 6}", "DEC b"] + instructionBuffer[bid+2], bid + 1)
        add_commands(["INC b", "SUB b c", "JZERO b 2 ", f"JUMP -{len(instructionBuffer[bid]) + len(instructionBuffer[bid + 1]) + 3}"],
                     bid + 1)
        add_commands(["INC b", "SUB b c",
                 f"JZERO b {len(instructionBuffer[bid])+len(instructionBuffer[bid+1])+1}"]
                 + instructionBuffer[bid] + instructionBuffer[bid+1], bid-1)
    else:
        add_commands(["INC b"] + instructionBuffer[bid+2] + [f"JUMP -{len(instructionBuffer[bid]) + len(instructionBuffer[bid + 1]) + 6 + len(instructionBuffer[bid+2])}"],
                     bid + 1)
        add_commands(["INC c", "SUB c b", "RESET b", "ADD b c",
                      f"JZERO b {len(instructionBuffer[bid]) + len(instructionBuffer[bid + 1]) +1}"]
                     + instructionBuffer[bid] + instructionBuffer[bid + 1], bid-1)
    instructionBuffer[bid+1] = insBufBack1
    instructionBuffer[bid+2] = insBufBack2

def obtain_tab_address(tab, reg, bid):
    ind = indexes.pop()
    mem_to_reg(reg, ind, bid)
    set_mem_reg(memory[tab[1]], bid)
    add_commands([f"ADD a {rtol[reg]}"], bid)
    set_register(reg, arrays[tab[1]][0], bid)
    add_commands([f"SUB a {rtol[reg]}"], bid)

def obtain_tab_value(tab, reg, bid):
    obtain_tab_address(tab, reg, bid)
    add_commands([f"LOAD {rtol[reg]} a"], bid)

def assign(a, b, bid):
    if a in iterators and a in declared:
        raise AlreadyDeclared(-1, a)
    if a in iterators and a in memory:
        raise IteratorModification(-1, a)
    elif a in iterators and a not in memory:
        raise NotDeclared(-1, a)

    if isinstance(b, str):
        mem_to_reg(1, memory[b], bid)
    elif isinstance(b, int):
        set_register(1, b, bid)
    elif isinstance(b, tuple) and b[0] == 'tab':
        mem_to_reg(1, memory[b[1]] + b[2], bid)
    elif isinstance(b, tuple) and b[0] == 'tabi':
        obtain_tab_value(b, 1, bid)

    if isinstance(a, str):
        reg_to_mem(1, memory[a], bid)
    elif isinstance(a, tuple) and a[0] == 'tab':
        reg_to_mem(1, memory[a[1]] + a[2], bid)
    elif isinstance(a, tuple) and a[0] == 'tabi':
        obtain_tab_address(a, 2, bid)
        add_commands(["STORE b a"], bid)


def evaluate_io(a, reg, bid, isRead):
    global memoryInd

    if isinstance(a, str):
        if a in iterators and a in memory and isRead:
            raise IteratorModification(a)
        set_register(0, memory[a], bid)
    elif isinstance(a, int):
        set_register(1, a, bid)
        reg_to_mem(1, memoryInd, bid)
        set_register(0, memoryInd, bid)
        memoryInd += 1
    elif isinstance(a, tuple) and a[0] == 'tab':
        set_register(0, memory[a[1]] + a[2], bid)
    elif isinstance(a, tuple) and a[0] == 'tabi':
        obtain_tab_address(a, reg, bid)

def io(a, bid, isRead):
    evaluate_io(a, 2 if isRead else 1, bid, isRead)
    add_commands(["GET a"] if isRead else ["PUT a"], bid)

def evaluate_operation(a, b, c, bid, rega=1, regb=2, performOperation=True):
    add_commands(setBuffer=bid)
    if isinstance(a, int) and isinstance(b, int) and performOperation:
        set_register(1, c, bid)
    else:
        for ev in [(b, regb), (a, rega)]:
            if isinstance(ev[0], tuple) and ev[0][0] == 'tab':
                mem_to_reg(ev[1], memory[ev[0][1]] + ev[0][2], bid)
            elif isinstance(ev[0], tuple) and ev[0][0] == 'tabi':
                obtain_tab_value(ev[0], ev[1], bid)
            elif isinstance(ev[0], int):
                set_register(ev[1], ev[0], bid)
            else:
                if ev[0] not in initialized:
                    raise NotInitialized(-1, ev[0])
                elif ev[0] not in memory:
                    raise NotDeclared(-1, ev[0])
                mem_to_reg(ev[1], memory[ev[0]], bid)
        return True

def neq(a, b, bid):
    if evaluate_operation(a, b, int(a != b) if isinstance(a, int) and isinstance(b, int) else -1, bid):
        add_commands(["RESET d", "ADD d c", "SUB d b", "SUB b c", "ADD b d"], bid)

def eq(a, b, bid):
    if evaluate_operation(a, b, int(a == b) if isinstance(a, int) and isinstance(b, int) else -1, bid):
        add_commands(["RESET e", "RESET d", "ADD d b", "SUB d c", "JZERO d 2", "JUMP 5",
                      "SUB c b", "JZERO c 2", "JUMP 2", "INC e", "RESET b", "ADD b e"], bid)

def ge(a, b, bid):
    if evaluate_operation(a, b, int(a >= b) if isinstance(a, int) and isinstance(b, int) else -1, bid):
        add_commands(["INC b", "SUB b c"], bid)

def le(a, b, bid):
    if evaluate_operation(a, b, int(a <= b) if isinstance(a, int) and isinstance(b, int) else -1, bid):
        add_commands(["INC c", "SUB c b", "RESET b", "ADD b c"], bid)

def gt(a, b, bid):
    if evaluate_operation(a, b, int(a > b) if isinstance(a, int) and isinstance(b, int) else -1, bid):
        add_commands(["SUB b c"], bid)

def lt(a, b, bid):
    if evaluate_operation(a, b, int(a < b) if isinstance(a, int) and isinstance(b, int) else -1, bid):
        add_commands(["SUB c b", "RESET b", "ADD b c"], bid)

def _if(b):
    add_commands([f"JZERO b {len(instructionBuffer[b]) + 1}"] + instructionBuffer[b], b - 1)

def _ifelse(b1, b2):
    add_commands([f"JZERO b {len(instructionBuffer[b1]) + 2}"] + instructionBuffer[b1] + [
        f"JUMP {len(instructionBuffer[b2]) + 1}"] + instructionBuffer[b2], b1 - 1)

def _while(b1, b2):
    add_commands(instructionBuffer[b1] + [f"JZERO b {len(instructionBuffer[b2]) + 2}"] + instructionBuffer[b2] + [
        f"JUMP -{len(instructionBuffer[b2]) + len(instructionBuffer[b1]) + 1}"], b1 - 1)

def _repeatuntil(b1, b2):
    add_commands(instructionBuffer[b1] + instructionBuffer[b2] + ["JZERO b 2", "JUMP 2",
                f"JUMP -{len(instructionBuffer[b1]) + len(instructionBuffer[b2]) + 2}"], b1 - 1)

def add(a, b, bid):
    if b != 0 and evaluate_operation(a, b, a + b if isinstance(a, int) and isinstance(b, int) else -1, bid) and b != 0:
        add_commands(["ADD b c"], bid)

def sub(a, b, bid):
    if evaluate_operation(a, b, a - b if isinstance(a, int) and isinstance(b, int) and a - b >= 0 else 0, bid) and b != 0:
        add_commands(["SUB b c"], bid)

def mul(a, b, bid):
    if evaluate_operation(a, b, a * b if isinstance(a, int) and isinstance(b, int) else -1, bid, 4):
        if b == 1:
            add_commands(["RESET b", "ADD b e"], bid)
        elif a == 2:
            add_commands(["RESET b","ADD b c", "SHL b"], bid)
        else:
            add_commands(["RESET a", "ADD a e", "SUB a c", "JZERO a 13", 'RESET a', 'ADD a c',
                      'RESET d', 'ADD d e', 'RESET b', 'JZERO d 19', 'JODD d 2', 'JUMP 2', 'ADD b a',
                      'SHL a', 'SHR d', 'JUMP -6', 'RESET a', 'ADD a e', 'RESET d', 'ADD d c', 'RESET b',
                      'JZERO d 7', 'JODD d 2', 'JUMP 2', 'ADD b a', 'SHL a', 'SHR d', 'JUMP -6'] if b != 2 else ["SHL b"], bid)

def div(a, b, bid, modulo=False):
    if a == 0 or b == 0:
        return set_register(1, 0, bid)
    c = a % b if modulo and isinstance(a, int) and isinstance(b, int) else (
        a // b if isinstance(a, int) and isinstance(b, int) else -1)
    if evaluate_operation(a, b, c, bid, 1, 5) and (b != 1 or modulo):
        add_commands(['RESET a', 'ADD a b', 'JZERO f 27', 'RESET d', 'ADD d f', 'RESET c', 'ADD c d', 'SUB c a',
                      'JZERO c 2', 'JUMP 3', 'SHL d', 'JUMP -6', 'RESET c', 'RESET e', 'ADD e d', 'SUB e a',
                      'JZERO e 4', 'SHL c', 'SHR d', 'JUMP 5', 'SHL c', 'INC c', 'SUB a d', 'SHR d',
                      'RESET e', 'ADD e f', 'SUB e d', 'JZERO e -14', 'JUMP 3', 'RESET a', 'RESET c',
                      'RESET b', 'ADD b a' if modulo else 'ADD b c'] if b != 2 or modulo else ["SHR b"], bid)

functions = {'+': add, '-': sub, '*': mul, '=': eq, '!=' : neq, '>' : gt, '<' : lt, '>=' : ge, '<=' : le}

dyn_tokens = {
    'NUM': '', 'PID': '[_a-z]+', 'LBRACKET': '\(', 'RBRACKET': '\)',
    'ASSIGN': ':=', 'SEMICOLON': ';', 'COLON': ':', 'COMMA': ',', 'LOWER': '<',
    'GREATER': '>', 'LOWEREQUAL': '<=', 'GREATEREQUAL': '>=', 'EQUAL': '=',
    'NOTEQUAL': '!=', 'ADD': '\+', 'SUB': '\-', 'MUL': '\*', 'DIV': '\/',
    'MOD': '\%', 'DECLARE': '', 'BEGIN': '', 'END': '', 'IF': '',
    'THEN': '', 'ELSE': '', 'ENDIF': '', 'WHILE': '', 'DO': '',
    'ENDWHILE': '', 'REPEAT': '', 'UNTIL': '', 'FOR': '', 'FROM': '',
    'TO': '', 'DOWNTO': '', 'ENDFOR': '', 'READ': '', 'WRITE': ''}

keywords = [_ for _ in dyn_tokens.keys() if dyn_tokens[_] == '']
tokens = list(dyn_tokens.keys())

for key, value in dyn_tokens.items():
    if key != False and value != '':
        vars()['t_' + key] = value

t_ignore = ' \t'
t_ignore_BLOCKCOMMENT = r'\[([^]]|[\r\n])*\]'

def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

def t_KEYWORD(t):
    r'[A-Z]+'
    if t.value in keywords:
        t.type = t.value
        return t
    else:
        raise BadKeyword(t.lexer.lineno, t.value)

def t_NUM(t):
    r'\d+'
    t.value = int(t.value)
    return t

def t_error(t):
    t.lexer.skip(1)

lexer = lex.lex()

precedence = (
    ('left', 'ADD', 'SUB'),
    ('left', 'MUL', 'DIV', 'MOD'),
)

def p_program(p):
    ''' program 	: DECLARE declarations BEGIN commands END
			        | BEGIN commands END '''
    p[0] = p[2] if len(p) == 4 else p[4]
    evaluate(p[0])
    add_commands(["HALT"],0)

def p_declarations_array(p):
    ''' declarations 	: PID LBRACKET NUM COLON NUM RBRACKET
		 	            | declarations COMMA PID LBRACKET NUM COLON NUM RBRACKET '''
    ind = 1 if len(p) == 7 else 3
    if p[ind + 2] > p[ind + 4]:
        raise InvalidArrayRange(p.lexer.lineno, p[ind + 2], p[ind + 4])
    p[0] = p[ind] if p[ind] not in declared else False
    if not p[0]:
        raise AlreadyDeclared(p.lexer.lineno, p[ind])
    declared.append(p[ind])
    arrays[p[ind]] = (p[ind + 2],p[ind + 4])

def p_declarations_pid(p):
    ''' declarations 	: PID
			            | declarations COMMA PID '''
    ind = 1 if len(p) == 2 else 3
    p[0] = p[ind] if p[ind] not in declared else False
    if not p[0]:
        raise AlreadyDeclared(p.lexer.lineno, p[ind])
    declared.append(p[ind])

def p_commands(p):
    ''' commands 	: command
                    | commands command '''
    if len(p) == 3:
        p[1].append(p[2])
        p[0] = p[1]
    else:
        p[0] = [p[1]]

def p_command_assign(p):
    ''' command	: identifier ASSIGN expression SEMICOLON '''
    p[0] = ("assign", p[1], p[3])

def p_command_if(p):
    ''' command	: IF condition THEN commands ENDIF
                | IF condition THEN commands ELSE commands ENDIF '''
    p[0] = ("if", p[2], p[4]) if len(p) == 6 else ("ifelse", p[2], p[4], p[6])

def p_command_while(p):
    ''' command	: WHILE condition DO commands ENDWHILE '''
    p[0] = ("while", p[2], p[4])

def p_command_repeat_until(p):
    ''' command	: REPEAT commands UNTIL condition SEMICOLON '''
    p[0] = ("repeat", p[2], p[4])

def p_iterator(p):
    ''' iterator	: PID '''
    p[0] = p[1]
    if p[1] in memory:
        raise AlreadyDeclared(p.lexer.lineno, p[1])
    iterators.append(p[1])

def p_command_for(p):
    ''' command	: FOR iterator FROM value TO value DO commands ENDFOR
            | FOR iterator FROM value DOWNTO value DO commands ENDFOR '''
    p[0] = ("for", p[2], p[4], p[6], p[8]) if p[5] == 'TO' else ("downfor", p[2], p[4], p[6], p[8])

def p_command_io(p):
    ''' command	: READ identifier SEMICOLON
            | WRITE value SEMICOLON '''
    p[0] = ("read", p[2]) if p[1] == 'READ' else ("write", p[2])

def p_expression_value(p):
    ''' expression : value '''
    p[0] = p[1]

def p_operation(p):
    '''expression : value ADD value
                  | value SUB value
                  | value MUL value
                  | value DIV value
                  | value MOD value'''
    p[0] = (p[2], p[1], p[3])

def p_condition(p):
    '''condition : value EQUAL value
                  | value NOTEQUAL value
                  | value LOWER value
                  | value GREATER value
                  | value LOWEREQUAL value
                  | value GREATEREQUAL value'''
    p[0] = (p[2], p[1], p[3])

def p_value_NUM(p):
    '''value : NUM '''
    p[0] = (p[1])

def p_value_identifier(p):
    '''value : identifier '''
    p[0] = (p[1])

def p_identifier_pid(p):
    '''identifier	: PID '''
    if p[1] not in declared and p[1] not in iterators:
        raise NotDeclared(p.lexer.lineno, p[1])
    if p[1] in arrays:
        raise NotAVariable(p.lexer.lineno, p[1])
    p[0] = (p[1])

def p_identifier_tab_id(p):
    '''identifier	: PID LBRACKET PID RBRACKET
                    | PID LBRACKET NUM RBRACKET '''
    if p[1] not in declared:
        raise NotDeclared(p.lexer.lineno, p[1])
    if p[1] not in arrays:
        raise NotAnArray(p.lexer.lineno, p[1])

    p[0] = ("tab", p[1], (p[3])) if isinstance(p[3], int) else ("tabi", p[1], (p[3]))

def p_error(p):
    if hasattr(p, 'type'):
        print("Błąd, nieprawidłowy znak: %s w linii %s" % (str(p.value), p.lineno))
    else:
        print("Błąd składni: " + str(p.value) + " " + str(p.lineno))
    sys.exit(0)

def evaluate(ex, bid=0, justassign=False):
    if 'i' in memory and memory['i'] == 106:
        pass
    global bufferId, memoryInd
    if isinstance(ex, list):
        bufferId = bid
        return "\n".join([str(evaluate(inst, bid)) for inst in ex])
    elif isinstance(ex, tuple):
        if ex[0] == 'read' or ex[0] == 'write':
            io(evaluate(ex[1], bid, (True if ex[0] == 'read' else False)), bid, True if ex[0] == 'read' else False)
        elif ex[0] == 'while' or ex[0] == 'repeat':
            clear_ins_buffer(bid+1)
            evaluate(ex[1], bid+1)
            clear_ins_buffer(bid+2)
            evaluate(ex[2], bid+2)
            _while(bid+1, bid+2) if ex[0] == 'while' else _repeatuntil(bid+1,bid+2)
        elif ex[0] == 'downfor' or ex[0] == 'for':
            if ex[1] in initialized:
                raise ReusedIterator(ex[1])
            memory[evaluate(ex[1], bid, True)] = memoryInd
            memoryInd += 1
            _from = evaluate(ex[2], bid)
            _to = evaluate(ex[3], bid)
            initialized.append(ex[1])
            clear_ins_buffer(bid + 1)
            evaluate(ex[4], bid + 1)
            _for(ex[1], _from, _to, False if ex[0] == 'for' else True, bid + 1)
            initialized.remove(evaluate(ex[1], bid))
            del memory[ex[1]]
            uiterators.remove(ex[1])
        elif ex[0] == 'if' or ex[0] == 'ifelse':
            clear_ins_buffer(bid+1)
            evaluate(ex[1], bid)
            evaluate(ex[2], bid + 1)
            if ex[0] == 'ifelse':
                clear_ins_buffer(bid + 2)
                evaluate(ex[3], bid + 2)
            _if(bid + 1) if ex[0] == 'if' else _ifelse(bid+1, bid+2)
        elif ex[0] == 'assign':
            assign(evaluate(ex[1], bid, True), evaluate(ex[2], bid), bid)
        elif ex[0] in functions:
            functions[ex[0]](evaluate(ex[1], bid), evaluate(ex[2], bid), bid)
        elif ex[0] == '/' or ex[0] == '%':
            div(evaluate(ex[1], bid), evaluate(ex[2], bid), bid, True if ex[0] == '%' else False)
        elif ex[0] == 'tab' or ex[0] == 'tabi':
            if ex[1] not in initialized:
                declare_variable(ex)
                initialized.append(ex[1])
            if ex[0] == 'tab':
                if ex[2] < arrays[ex[1]][0] or ex[2] > arrays[ex[1]][1]:
                    raise InvalidArrayElement(ex[2], ex[1])
                return (ex[0], ex[1], ex[2] - arrays[ex[1]][0])
            else:
                if ex[2] not in declared and ex[2] not in iterators and not justassign:
                    raise NotDeclared(-1, str(ex[2]))
                if ex[2] not in initialized and not justassign:
                    raise NotInitialized(ex[2])
                indexes.append(memory[evaluate(ex[2], bid)])
        return ex
    else:
        if isinstance(ex, str) and ex in iterators and ex not in uiterators and not justassign:
            uiterators.append(ex)
        if isinstance(ex, str) and ex not in declared and ex not in iterators and not justassign:
            raise NotDeclared(-1, str(ex))
        if isinstance(ex, str) and ex not in initialized and not justassign:
            raise NotInitialized(ex)
        if isinstance(ex, str) and ex not in initialized and ex not in iterators:
            declare_variable(ex)
            initialized.append(ex)
        return ex

parser = yacc.yacc()

with open(sys.argv[1], 'r') as fp:
    content = fp.read()
    try:
        parser.parse(content)
        print('\n'.join(instructions))
    except Exception as e:
        print(traceback.format_exc())
