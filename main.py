import copy

import ply.lex as lex
import ply.yacc as yacc
import sys
from exceptions import *
import traceback

memoryInd = 0
instructions, variables, iterators, indexes, arrays, usages, memory, instructionBuffer = [], [], [], [], {}, {}, {}, {}
initialized = []
rtol = ["a", "b", "c", "d", "e", "f"]
bufferId = 0

def check_whether_initialized(a):
    if str(a) not in initialized:
        raise NotInitialized(str(a))

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


def declare_variable(name, length=None, a=None, b=None, isIterator=False):
    global memory, memoryInd
    if isIterator and name in memory:
        raise AlreadyDeclared(-1,name)

    memory[name] = memoryInd
    variables.append(name)
    if length is not None:
        memoryInd += length
        arrays[name] = (a, b)
    else:
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
    memory[f"{iterator}_e"] = memoryInd
    reg_to_mem(1, memory[f"{iterator}"], bid-1)
    reg_to_mem(2, memory[f"{iterator}_e"], bid-1)
    insBufBack = copy.deepcopy(instructionBuffer[bid+1]) if bid+1 in instructionBuffer else []
    clear_ins_buffer(bid+1)
    mem_to_reg(1,memory[f"{iterator}"], bid+1)
    add_commands([("DEC b" if reverse else "INC b"), "STORE b a"], bid+1)
    mem_to_reg(2,memory[f"{iterator}_e"], bid+1)
    add_commands([f"JUMP -{len(instructionBuffer[bid])+len(instructionBuffer[bid+1])+(3 if reverse else 5)}"], bid+1)
    if reverse:
        add_commands(["INC c", "SUB b c",
                 f"JZERO b {len(instructionBuffer[bid])+len(instructionBuffer[bid+1])+1}"]
                 + instructionBuffer[bid] + instructionBuffer[bid+1], bid-1)
    else:
        add_commands(["INC c", "SUB c b", "RESET b", "ADD b c",
                      f"JZERO b {len(instructionBuffer[bid]) + len(instructionBuffer[bid + 1]) + 1}"]
                     + instructionBuffer[bid] + instructionBuffer[bid + 1], bid - 1)
    instructionBuffer[bid+1] = insBufBack

def _for(iterator, _from, _to, reverse, bid):
    global memoryInd, instructionBuffer
    evaluate_operation(_from, _to, 0, bid-1, performOperation=False)
    memory[f"{iterator}_e"] = memoryInd
    memoryInd += 1
    reg_to_mem(1, memory[f"{iterator}"], bid-1)
    reg_to_mem(2, memory[f"{iterator}_e"], bid-1)
    insBufBack = copy.deepcopy(instructionBuffer[bid+1]) if bid+1 in instructionBuffer else []
    clear_ins_buffer(bid+1)
    mem_to_reg(1,memory[f"{iterator}"], bid+1)
    mem_to_reg(2,memory[f"{iterator}_e"], bid+1)
    add_commands(["DEC b"] if reverse else ["INC b"], bid + 1)
    reg_to_mem(1, memory[f"{iterator}"], bid + 1)
    add_commands([f"JUMP -{len(instructionBuffer[bid]) + len(instructionBuffer[bid + 1]) + (3 if reverse else 5)}"], bid + 1)
    if reverse:
        add_commands(["INC c", "SUB c b",
                 f"JZERO b {len(instructionBuffer[bid])+len(instructionBuffer[bid+1])+1}"]
                 + instructionBuffer[bid] + instructionBuffer[bid+1], bid-1)
    else:
        add_commands(["INC c", "SUB c b", "RESET b", "ADD b c",
                      f"JZERO b {len(instructionBuffer[bid]) + len(instructionBuffer[bid + 1]) + 1}"]
                     + instructionBuffer[bid] + instructionBuffer[bid + 1], bid-1)
    instructionBuffer[bid+1] = insBufBack


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
    if a in iterators and a in memory:
        raise IteratorModification(-1, a)
    # TODO: dokładny warunek inicjalizacji tablicy
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

    if str(a) not in initialized:
        initialized.append(str(a))


def evaluate_io(a, reg, bid, isWrite):
    global memoryInd
    if isinstance(a, str):
        set_register(0, memory[a], bid)
        if isWrite:
            initialized.append(a)
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
    add_commands(instructionBuffer[b2] + instructionBuffer[b1] + ["JZERO b 2", "JUMP 2",
                f"JUMP -{len(instructionBuffer[b1]) + len(instructionBuffer[b2]) + 2}"], b1 - 1)


def add(a, b, bid):
    if evaluate_operation(a, b, a + b if isinstance(a, int) and isinstance(b, int) else -1, bid):
        add_commands(["ADD b c"], bid)


def sub(a, b, bid):
    if evaluate_operation(a, b, a - b if isinstance(a, int) and isinstance(b, int) and a - b >= 0 else 0, bid):
        add_commands(["SUB b c"], bid)


def mul(x, y, bid):
    if evaluate_operation(x, y, x * y if isinstance(x, int) and isinstance(y, int) else -1, bid, 4):
        add_commands(["RESET a", "ADD a e", "SUB a c", "JZERO a 13", 'RESET a', 'ADD a c',
                      'RESET d', 'ADD d e', 'RESET b', 'JZERO d 19', 'JODD d 2', 'JUMP 2', 'ADD b a',
                      'SHL a', 'SHR d', 'JUMP -6', 'RESET a', 'ADD a e', 'RESET d', 'ADD d c', 'RESET b',
                      'JZERO d 7', 'JODD d 2', 'JUMP 2', 'ADD b a', 'SHL a', 'SHR d', 'JUMP -6'], bid)


def div(x, y, bid, modulo=False):
    if isinstance(y, int) and y == 0:
        return set_register(1, 0, bid)
    # nienawidzę się za te linijkę
    c = x % y if modulo and isinstance(x, int) and isinstance(y, int) else (
        x // y if isinstance(x, int) and isinstance(y, int) else -1)
    if evaluate_operation(x, y, c, bid, 0, 5):
        add_commands(['JZERO f 27', 'RESET d', 'ADD d f', 'RESET c', 'ADD c d', 'SUB c a',
                      'JZERO c 2', 'JUMP 3', 'SHL d', 'JUMP -6', 'RESET c', 'RESET e', 'ADD e d', 'SUB e a',
                      'JZERO e 4', 'SHL c', 'SHR d', 'JUMP 5', 'SHL c', 'INC c', 'SUB a d', 'SHR d',
                      'RESET e', 'ADD e f', 'SUB e d', 'JZERO e -14', 'JUMP 3', 'RESET a', 'RESET c',
                      'RESET b', 'ADD b a' if modulo else 'ADD b c'], bid)


functions = {'+': add, '-': sub, '*': mul, 'assign': assign, '=': eq, '!=' : neq, '>' : gt, '<' : lt, '>=' : ge, '<=' : le}

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
    p[0] = p[ind] if p[ind] not in variables else False
    if not p[0]:
        raise AlreadyDeclared(p.lexer.lineno, p[ind])
    declare_variable(p[ind], p[ind + 4] - p[ind + 2] + 1, p[ind + 2], p[ind + 4])


def p_declarations_pid(p):
    ''' declarations 	: PID
			            | declarations COMMA PID '''
    ind = 1 if len(p) == 2 else 3
    p[0] = p[ind] if p[ind] not in variables else False
    if not p[0]:
        raise AlreadyDeclared(p.lexer.lineno, p[ind])
    declare_variable(p[ind])


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
    # TODO: Sprawdzanie czy okej
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
    if p[1] not in memory and p[1] not in iterators:
        raise NotDeclared(p.lexer.lineno, p[1])
    if p[1] in arrays:
        raise NotAVariable(p.lexer.lineno, p[1])
    p[0] = (p[1])


def p_identifier_tab_id(p):
    '''identifier	: PID LBRACKET PID RBRACKET
                    | PID LBRACKET NUM RBRACKET '''
    if p[1] not in memory:
        raise NotDeclared(p.lexer.lineno, p[1])
    if p[1] not in arrays:
        raise NotAnArray(p.lexer.lineno, p[1])

    p[0] = ("tab", p[1], (p[3])) if isinstance(p[3], int) else ("tabi", p[1], (p[3]))


def p_error(p):
    print(traceback.format_exc())
    if hasattr(p, 'type'):
        showerror("Syntax Err. Misplaced sign: %s at %s" % (str(p.value), p.lineno))
    else:
        showerror("Syntax Err: " + str(p.value) + " " + str(p.lineno))
    sys.exit(0)


def showerror(msg):
    sys.exit(msg)

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
        elif ex[0] == 'while':
            clear_ins_buffer(bid+1, bid+2)
            evaluate(ex[1], bid + 1)
            evaluate(ex[2], bid + 2)
            _while(bid + 1, bid + 2, )
        elif ex[0] == 'repeat':
            clear_ins_buffer(bid+1, bid+2)
            evaluate(ex[2], bid + 1)
            evaluate(ex[1], bid + 2)
            _repeatuntil(bid + 1, bid + 2)
        elif ex[0] == 'for':
            if ex[1] in initialized:
                raise ReusedIterator(ex[1])
            memory[evaluate(ex[1], bid, True)] = memoryInd
            memoryInd += 1
            _from = evaluate(ex[2], bid)
            _to = evaluate(ex[3], bid)
            initialized.append(ex[1])
            clear_ins_buffer(bid + 1)
            evaluate(ex[4], bid + 1)
            _for(ex[1], _from, _to, False, bid+1)
            initialized.remove(evaluate(ex[1], bid))
            del memory[ex[1]]
        elif ex[0] == 'downfor':
            memory[ex[1]] = memoryInd
            memoryInd += 1
            initialized.append(ex[1])
            clear_ins_buffer(bid + 1)
            evaluate(ex[4], bid + 1)
            _for(ex[1], evaluate(ex[2], bid), evaluate(ex[3], bid), True, bid + 1)
            initialized.remove(evaluate(ex[1], bid))
        elif ex[0] == 'if':
            clear_ins_buffer(bid+1)
            evaluate(ex[1], bid)
            evaluate(ex[2], bid + 1)
            _if(bid + 1)
        elif ex[0] == 'ifelse':
            clear_ins_buffer(bid+1, bid+2)
            evaluate(ex[1], bid)
            evaluate(ex[2], bid + 1)
            evaluate(ex[3], bid + 2)
            _ifelse(bid + 1, bid + 2)
        elif ex[0] == 'assign':
            assign(evaluate(ex[1], bid, True), evaluate(ex[2], bid), bid)
        elif ex[0] == '+' or ex[0] == '-' or ex[0] == '*'  or ex[0] == '=' or ex[0] == '!=' or ex[0] == '>' or ex[0] == '<' or ex[0] == '>=' or ex[0] == '<=':
            functions[ex[0]](evaluate(ex[1], bid), evaluate(ex[2], bid), bid)
        elif ex[0] == '/' or ex[0] == '%':
            div(evaluate(ex[1], bid), evaluate(ex[2], bid), bid, True if ex[0] == '%' else False)
        elif ex[0] == 'tab':
            return (ex[0], ex[1], ex[2] - arrays[ex[1]][0])
        elif ex[0] == 'tabi':
            indexes.append(memory[evaluate(ex[2],bid)])
        return ex
    else:
        if isinstance(ex, str) and ex not in initialized and not justassign:
            raise NotInitialized(ex)
        return ex


parser = yacc.yacc()

with open(sys.argv[1], 'r') as fp:
    content = fp.read()
    try:
        parser.parse(content)
        print('\n'.join(instructions))
    except Exception as e:
        print(traceback.format_exc())

