%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% VIOLATIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

int: RULES = 6;

array[1..RULES] of var int: V;

array[1..RULES] of string: RULE_NAME =
[
    "AMRITA",      %1
    "GREG NATHAN",
     "Martin Lew",
      "TERESA",
      "BRENDON" ,    %5
      "REBECCA", 
];

constraint
    rule(true, V[1], test_amrita(avarma))       /\
    rule(true, V[2], test_greg_nathan(gnathan)) /\
    rule(true, V[3], test_martin_lew(mlew))     /\
    rule(true, V[4], test_teresa(tbridga))      /\
    rule(true, V[5], test_brendon(bmc))         /\  
    rule(true, V[6], test_rm(rmarson))         

;


%% put production predicats here --- 



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% RULE FRAMEWORK
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

int: HARD = 100;

predicate rule(
    bool: is_hard,
    var int: v,
    var bool: cond
) =
(
    v >=
        (if cond then 0
         elseif is_hard then HARD
         else 1
         endif)
);


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% OBJECTIVE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

solve minimize sum(i in 1..RULES)(V[i])

    + 1000 * total_am_shortfall
    + 1000 * total_pm_shortfall;
  



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% OUTPUT
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

output
[
    "\nSTAFF VIOLATIONS\n\n"
]
++
[
    if fix(V[i]) > 0 then
        " --> "
        ++ RULE_NAME[i]
        ++ " (V="
        ++ show(V[i])
        ++ ")\n"
    else
        ""
    endif
    | i in 1..RULES
];

