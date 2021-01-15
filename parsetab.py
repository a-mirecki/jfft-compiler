
# parsetab.py
# This file is automatically generated. Do not edit.
# pylint: disable=W,C,R
_tabversion = '3.10'

_lr_method = 'LALR'

_lr_signature = 'leftADDSUBleftMULDIVMODADD ASSIGN BEGIN COLON COMMA DECLARE DIV DO DOWNTO ELSE END ENDFOR ENDIF ENDWHILE EQUAL FOR FROM GREATER GREATEREQUAL IF LBRACKET LOWER LOWEREQUAL MOD MUL NOTEQUAL NUM PID RBRACKET READ REPEAT SEMICOLON SUB THEN TO UNTIL WHILE WRITE program \t: DECLARE declarations BEGIN commands END\n\t\t\t        | BEGIN commands END  declarations \t: PID LBRACKET NUM COLON NUM RBRACKET\n\t\t \t            | declarations COMMA PID LBRACKET NUM COLON NUM RBRACKET  declarations \t: PID\n\t\t\t            | declarations COMMA PID  commands \t: command\n                    | commands command  command\t: identifier ASSIGN expression SEMICOLON  command\t: IF condition THEN commands ENDIF\n                | IF condition THEN commands ELSE commands ENDIF  command\t: WHILE condition DO commands ENDWHILE  command\t: REPEAT commands UNTIL condition SEMICOLON  iterator\t: PID  command\t: FOR iterator FROM value TO value DO commands ENDFOR\n            | FOR iterator FROM value DOWNTO value DO commands ENDFOR  command\t: READ identifier SEMICOLON\n            | WRITE value SEMICOLON  expression : value expression : value ADD value\n                  | value SUB value\n                  | value MUL value\n                  | value DIV value\n                  | value MOD valuecondition : value EQUAL value\n                  | value NOTEQUAL value\n                  | value LOWER value\n                  | value GREATER value\n                  | value LOWEREQUAL value\n                  | value GREATEREQUAL valuevalue : NUM value : identifier identifier\t: PID identifier\t: PID LBRACKET PID RBRACKET\n                    | PID LBRACKET NUM RBRACKET '
    
_lr_action_items = {'DECLARE':([0,],[2,]),'BEGIN':([0,4,5,34,87,95,],[3,16,-5,-6,-3,-4,]),'$end':([1,19,52,],[0,-2,-1,]),'PID':([2,3,6,7,9,10,11,12,13,14,16,17,20,21,27,32,33,38,39,40,41,42,43,44,45,46,47,48,49,55,56,57,58,59,60,61,68,80,81,82,83,84,85,88,92,93,94,96,97,98,99,],[5,15,15,-7,15,15,15,29,15,15,15,34,-8,15,15,50,15,15,15,15,15,15,15,15,15,15,15,-17,-18,-9,15,15,15,15,15,15,15,-10,15,-12,-13,15,15,15,-11,15,15,15,15,-15,-16,]),'IF':([3,6,7,11,16,20,27,33,38,45,48,49,55,61,68,80,81,82,83,88,92,93,94,96,97,98,99,],[9,9,-7,9,9,-8,9,9,9,9,-17,-18,-9,9,9,-10,9,-12,-13,9,-11,9,9,9,9,-15,-16,]),'WHILE':([3,6,7,11,16,20,27,33,38,45,48,49,55,61,68,80,81,82,83,88,92,93,94,96,97,98,99,],[10,10,-7,10,10,-8,10,10,10,10,-17,-18,-9,10,10,-10,10,-12,-13,10,-11,10,10,10,10,-15,-16,]),'REPEAT':([3,6,7,11,16,20,27,33,38,45,48,49,55,61,68,80,81,82,83,88,92,93,94,96,97,98,99,],[11,11,-7,11,11,-8,11,11,11,11,-17,-18,-9,11,11,-10,11,-12,-13,11,-11,11,11,11,11,-15,-16,]),'FOR':([3,6,7,11,16,20,27,33,38,45,48,49,55,61,68,80,81,82,83,88,92,93,94,96,97,98,99,],[12,12,-7,12,12,-8,12,12,12,12,-17,-18,-9,12,12,-10,12,-12,-13,12,-11,12,12,12,12,-15,-16,]),'READ':([3,6,7,11,16,20,27,33,38,45,48,49,55,61,68,80,81,82,83,88,92,93,94,96,97,98,99,],[13,13,-7,13,13,-8,13,13,13,13,-17,-18,-9,13,13,-10,13,-12,-13,13,-11,13,13,13,13,-15,-16,]),'WRITE':([3,6,7,11,16,20,27,33,38,45,48,49,55,61,68,80,81,82,83,88,92,93,94,96,97,98,99,],[14,14,-7,14,14,-8,14,14,14,14,-17,-18,-9,14,14,-10,14,-12,-13,14,-11,14,14,14,14,-15,-16,]),'COMMA':([4,5,34,87,95,],[17,-5,-6,-3,-4,]),'LBRACKET':([5,15,34,],[18,32,53,]),'END':([6,7,20,33,48,49,55,80,82,83,92,98,99,],[19,-7,-8,52,-17,-18,-9,-10,-12,-13,-11,-15,-16,]),'UNTIL':([7,20,27,48,49,55,80,82,83,92,98,99,],[-7,-8,46,-17,-18,-9,-10,-12,-13,-11,-15,-16,]),'ENDIF':([7,20,48,49,55,61,80,82,83,88,92,98,99,],[-7,-8,-17,-18,-9,80,-10,-12,-13,92,-11,-15,-16,]),'ELSE':([7,20,48,49,55,61,80,82,83,92,98,99,],[-7,-8,-17,-18,-9,81,-10,-12,-13,-11,-15,-16,]),'ENDWHILE':([7,20,48,49,55,68,80,82,83,92,98,99,],[-7,-8,-17,-18,-9,82,-10,-12,-13,-11,-15,-16,]),'ENDFOR':([7,20,48,49,55,80,82,83,92,96,97,98,99,],[-7,-8,-17,-18,-9,-10,-12,-13,-11,98,99,-15,-16,]),'ASSIGN':([8,15,71,72,],[21,-33,-34,-35,]),'NUM':([9,10,14,18,21,32,39,40,41,42,43,44,46,47,53,54,56,57,58,59,60,84,85,86,],[24,24,24,35,24,51,24,24,24,24,24,24,24,24,73,74,24,24,24,24,24,24,24,91,]),'EQUAL':([15,23,24,25,71,72,],[-33,39,-31,-32,-34,-35,]),'NOTEQUAL':([15,23,24,25,71,72,],[-33,40,-31,-32,-34,-35,]),'LOWER':([15,23,24,25,71,72,],[-33,41,-31,-32,-34,-35,]),'GREATER':([15,23,24,25,71,72,],[-33,42,-31,-32,-34,-35,]),'LOWEREQUAL':([15,23,24,25,71,72,],[-33,43,-31,-32,-34,-35,]),'GREATEREQUAL':([15,23,24,25,71,72,],[-33,44,-31,-32,-34,-35,]),'SEMICOLON':([15,24,25,30,31,36,37,62,63,64,65,66,67,69,71,72,75,76,77,78,79,],[-33,-31,-32,48,49,55,-19,-25,-26,-27,-28,-29,-30,83,-34,-35,-20,-21,-22,-23,-24,]),'ADD':([15,24,25,37,71,72,],[-33,-31,-32,56,-34,-35,]),'SUB':([15,24,25,37,71,72,],[-33,-31,-32,57,-34,-35,]),'MUL':([15,24,25,37,71,72,],[-33,-31,-32,58,-34,-35,]),'DIV':([15,24,25,37,71,72,],[-33,-31,-32,59,-34,-35,]),'MOD':([15,24,25,37,71,72,],[-33,-31,-32,60,-34,-35,]),'THEN':([15,22,24,25,62,63,64,65,66,67,71,72,],[-33,38,-31,-32,-25,-26,-27,-28,-29,-30,-34,-35,]),'DO':([15,24,25,26,62,63,64,65,66,67,71,72,89,90,],[-33,-31,-32,45,-25,-26,-27,-28,-29,-30,-34,-35,93,94,]),'TO':([15,24,25,70,71,72,],[-33,-31,-32,84,-34,-35,]),'DOWNTO':([15,24,25,70,71,72,],[-33,-31,-32,85,-34,-35,]),'FROM':([28,29,],[47,-14,]),'COLON':([35,73,],[54,86,]),'RBRACKET':([50,51,74,91,],[71,72,87,95,]),}

_lr_action = {}
for _k, _v in _lr_action_items.items():
   for _x,_y in zip(_v[0],_v[1]):
      if not _x in _lr_action:  _lr_action[_x] = {}
      _lr_action[_x][_k] = _y
del _lr_action_items

_lr_goto_items = {'program':([0,],[1,]),'declarations':([2,],[4,]),'commands':([3,11,16,38,45,81,93,94,],[6,27,33,61,68,88,96,97,]),'command':([3,6,11,16,27,33,38,45,61,68,81,88,93,94,96,97,],[7,20,7,7,20,20,7,7,20,20,7,20,7,7,20,20,]),'identifier':([3,6,9,10,11,13,14,16,21,27,33,38,39,40,41,42,43,44,45,46,47,56,57,58,59,60,61,68,81,84,85,88,93,94,96,97,],[8,8,25,25,8,30,25,8,25,8,8,8,25,25,25,25,25,25,8,25,25,25,25,25,25,25,8,8,8,25,25,8,8,8,8,8,]),'condition':([9,10,46,],[22,26,69,]),'value':([9,10,14,21,39,40,41,42,43,44,46,47,56,57,58,59,60,84,85,],[23,23,31,37,62,63,64,65,66,67,23,70,75,76,77,78,79,89,90,]),'iterator':([12,],[28,]),'expression':([21,],[36,]),}

_lr_goto = {}
for _k, _v in _lr_goto_items.items():
   for _x, _y in zip(_v[0], _v[1]):
       if not _x in _lr_goto: _lr_goto[_x] = {}
       _lr_goto[_x][_k] = _y
del _lr_goto_items
_lr_productions = [
  ("S' -> program","S'",1,None,None,None),
  ('program -> DECLARE declarations BEGIN commands END','program',5,'p_program','main.py',188),
  ('program -> BEGIN commands END','program',3,'p_program','main.py',189),
  ('declarations -> PID LBRACKET NUM COLON NUM RBRACKET','declarations',6,'p_declarations_array','main.py',197),
  ('declarations -> declarations COMMA PID LBRACKET NUM COLON NUM RBRACKET','declarations',8,'p_declarations_array','main.py',198),
  ('declarations -> PID','declarations',1,'p_declarations_pid','main.py',208),
  ('declarations -> declarations COMMA PID','declarations',3,'p_declarations_pid','main.py',209),
  ('commands -> command','commands',1,'p_commands','main.py',217),
  ('commands -> commands command','commands',2,'p_commands','main.py',218),
  ('command -> identifier ASSIGN expression SEMICOLON','command',4,'p_command_assign','main.py',226),
  ('command -> IF condition THEN commands ENDIF','command',5,'p_command_if','main.py',230),
  ('command -> IF condition THEN commands ELSE commands ENDIF','command',7,'p_command_if','main.py',231),
  ('command -> WHILE condition DO commands ENDWHILE','command',5,'p_command_while','main.py',235),
  ('command -> REPEAT commands UNTIL condition SEMICOLON','command',5,'p_command_repeat_until','main.py',239),
  ('iterator -> PID','iterator',1,'p_iterator','main.py',243),
  ('command -> FOR iterator FROM value TO value DO commands ENDFOR','command',9,'p_command_for','main.py',249),
  ('command -> FOR iterator FROM value DOWNTO value DO commands ENDFOR','command',9,'p_command_for','main.py',250),
  ('command -> READ identifier SEMICOLON','command',3,'p_command_io','main.py',254),
  ('command -> WRITE value SEMICOLON','command',3,'p_command_io','main.py',255),
  ('expression -> value','expression',1,'p_expression_value','main.py',259),
  ('expression -> value ADD value','expression',3,'p_operation','main.py',263),
  ('expression -> value SUB value','expression',3,'p_operation','main.py',264),
  ('expression -> value MUL value','expression',3,'p_operation','main.py',265),
  ('expression -> value DIV value','expression',3,'p_operation','main.py',266),
  ('expression -> value MOD value','expression',3,'p_operation','main.py',267),
  ('condition -> value EQUAL value','condition',3,'p_condition','main.py',271),
  ('condition -> value NOTEQUAL value','condition',3,'p_condition','main.py',272),
  ('condition -> value LOWER value','condition',3,'p_condition','main.py',273),
  ('condition -> value GREATER value','condition',3,'p_condition','main.py',274),
  ('condition -> value LOWEREQUAL value','condition',3,'p_condition','main.py',275),
  ('condition -> value GREATEREQUAL value','condition',3,'p_condition','main.py',276),
  ('value -> NUM','value',1,'p_value_NUM','main.py',280),
  ('value -> identifier','value',1,'p_value_identifier','main.py',284),
  ('identifier -> PID','identifier',1,'p_identifier_pid','main.py',296),
  ('identifier -> PID LBRACKET PID RBRACKET','identifier',4,'p_identifier_tab_id','main.py',300),
  ('identifier -> PID LBRACKET NUM RBRACKET','identifier',4,'p_identifier_tab_id','main.py',301),
]
