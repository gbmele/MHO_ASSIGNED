
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% VIOLATIONS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

int: RULES = 19;

array[1..RULES] of var int: V;

array[1..RULES] of string: RULE_NAME =
[
    "AMRITA",      %1
    "GREG NATHAN",
     "Martin Lew",
      "TERESA",
      "BRENDON" ,    %5
      "REBECCA",
      "MIN",       %7 
      "CARLOS",    %8
      "DINH BUI",  %9
      "G_MELE",    %10
      "JAMES_LIM", %11
      "DAVID LOWMAN",   %12
      "CHRIS KNIGHT",    %13
      "KIMSON VU",        %14
      "SADHNA K",  %15
      "DAMIEN",    %16
      "BEN_LEE",    %17
      "jannet",      %18
      "all as is",
];

constraint
    rule(true, V[1],  test_amrita(avarma))       /\
    rule(true, V[2],  true) /\ % test_greg_nathan(gnathan)) /\
    rule(true, V[3],  test_martin_lew(mlew))     /\
    rule(true, V[4],  test_teresa(tbridga))      /\
    rule(true, V[5],  test_brendon(bmc))         /\  
    rule(true, V[6],  test_rm(rmarson))          /\
    rule(true, V[7],  test_min(mchong))          /\          
    rule(true, V[8],  test_carlos(ccobela))      /\          
    rule(true, V[9],  test_db(dbui))             /\          
    rule(true, V[10], test_gm(gmele))            /\
    rule(true, V[11], test_jlim(jlim))           /\
    rule(true, V[12], test_dl(dlowman))          /\       
    rule(true, V[13], test_cknight(cknight))     /\          
    rule(true, V[14], test_kimson(kvu))          /\  
    rule(true, V[15], test_sk(skapita))          /\
    rule(true, V[16], test_damien(dhezeki))      /\   
    rule(true, V[17], test_ben_lee(blee))        /\  
    rule(true, V[18], test_jannet(jchan))        /\
    rule(true, V[19], roster_as_is(parcher) /\ 
                      roster_as_is(yperera) %  /\
                      %roster_as_is(mlynch)  /\
                      %roster_as_is(aroseng)  /\
                      %roster_as_is(lbridgf)  /\
                      %roster_as_is(lsmith)   /\
                      %roster_as_is(hlauren) 
        ) 

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

%%%%THNNING OUTPUT
%%%%%
output
[
   if fix(V[r]) = 0 then "."
   elseif fix(V[r]) < 100 then "+"
   else "*"
   endif
   | r in 1..RULES
];

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% OBJECTIVE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

solve minimize sum(i in 1..RULES)(V[i])

    + 1000 * total_am_shortfall
    + 1000 * total_pm_shortfall
    
    + 10000 * min_chong_mon_am
    + 10000 * david_lowman_min_thursday


;
  



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% OUTPUT
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

output
[
    "\nSTAFF VIOLATIONS\n\n"
]
++
[
    if fix(V[r]) > 0 then
        " --> "
        ++ RULE_NAME[r]
        ++ " (V="
        ++ show(V[r])
        ++ ")\n"
    else
        ""
    endif
    | r in 1..RULES
];

output["\n\nOTHER MINIMIZERS\n"];
output["min chong min mon am \(min_chong_mon_am) \n"];
output["david lowman min thursday \(david_lowman_min_thursday) \n"];



%%%% put all the test_docs+for_this_cost_center_here


