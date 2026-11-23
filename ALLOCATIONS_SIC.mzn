%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SIC LAYER  
%            later on call this the ROLE layer
% alloc determines who is AM / PM / C
%
% role determines who is:
%   SSU
%   INC
%   OC
%
% Rules:
%
%   exactly one SSU per day
%   exactly one INC per day
%   exactly one OC per day
%
%   SSU must be AM
%   INC must be AM
%   OC  must be PM
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

enum ROLE = { NONE, SSU, INC, OC};

array[docs,days] of var ROLE: role;


%%TEMP CHANNEL TO ALLOW ROSTER ZERO TO WORK


constraint forall(doc in docs,day in days) (set_ROLE(doc,0,15,0,15,0,15));


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DAILY COVERAGE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint forall(day in days) (sum(doc in docs)(bool2int(role[doc,day] = SSU)) = 1);

constraint forall(day in days) (sum(doc in docs)(bool2int(role[doc,day] = INC)) = 1);

constraint forall(day in days) (sum(doc in docs)(bool2int(role[doc,day] =  OC)) = 1);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% CHANNEL SIC -> ALLOC
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint forall(doc in docs, day in days)
    (role[doc,day] = SSU -> alloc[doc,day,AM] = 1);
constraint forall(doc in docs, day in days)

    (role[doc,day] = INC -> alloc[doc,day,AM] = 1);

constraint forall(doc in docs, day in days)
    (role[doc,day] = OC -> alloc[doc,day,PM]  = 1);




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% COUNTS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

array[docs] of var 0..DAYS: n_ssu;
array[docs] of var 0..DAYS: n_inc;
array[docs] of var 0..DAYS: n_occ;

constraint forall(doc in docs)(
    n_ssu[doc] =
        sum(day in days)(
            bool2int(role[doc,day] = SSU)
        )
);

constraint forall(doc in docs)(
    n_inc[doc] =
        sum(day in days)(
            bool2int(role[doc,day] = INC)
        )
);

constraint forall(doc in docs)(
    n_occ[doc] =
        sum(day in days)(
            bool2int(role[doc,day] = OC)
        )
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TARGETS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

array[docs] of var int: target_ssu;
array[docs] of var int: target_inc;
array[docs] of var int: target_occ;

array[docs] of var int: min_ssu;
array[docs] of var int: min_inc;
array[docs] of var int: min_occ;

constraint forall(doc in docs)(
    n_ssu[doc] >= min_ssu[doc]
    /\
    n_ssu[doc] <= target_ssu[doc]
);

constraint forall(doc in docs)(
    n_inc[doc] >= min_inc[doc]
    /\
    n_inc[doc] <= target_inc[doc]
);

constraint forall(doc in docs)(
    n_occ[doc] >= min_occ [doc]
    /\
    n_occ[doc] <= target_occ[doc]
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% GAPS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%int: min_ssu_gap = 2;
%int: min_inc_gap = 2;
%int: min_oc_gap  = 9;

constraint
forall(doc in docs,
       day in 1..DAYS-min_ssu_gap+1)(
    sum(d in day..day+min_ssu_gap-1)(
        bool2int(role[doc,d] = SSU)
    ) <= 1
);

constraint
forall(doc in docs,
       day in 1..DAYS-min_inc_gap+1)(
    sum(d in day..day+min_inc_gap-1)(
        bool2int(role[doc,d] = INC)
    ) <= 1
);

constraint
forall(doc in docs,
       day in 1..DAYS-min_oc_gap+1)(
    sum(d in day..day+min_oc_gap-1)(
        bool2int(role[doc,d] = OC)
    ) <= 1
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% FAIRNESS SETTER
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

predicate set_ROLE(
    docs: doc,
    int: minSSU,
    int: targetSSU,
    int: minINC,
    int: targetINC,
    int: minOC,
    int: targetOC
) =
(
    min_ssu[doc]    = minSSU
    /\
    target_ssu[doc] = targetSSU

    /\
    min_inc[doc]    = minINC
    /\
    target_inc[doc] = targetINC

    /\
    min_oc[doc]     = minOC
    /\
    target_occ[doc]  = targetOC
);


output [
  "SSU,"
  ++ concat([
       concat([show(d)
               | d in docs
               where fix(role[d,day])=SSU])
       ++ ","
       | day in days
     ])
  ++ "\n\n",

  "INC,"
  ++ concat([
       concat([show(d)
               | d in docs
               where fix(role[d,day])=INC])
       ++ ","
       | day in days
     ])
  ++ "\n\n",

  "OC,"
  ++ concat([
       concat([show(d)
               | d in docs
               where fix(role[d,day])=OC])
       ++ ","
       | day in days
     ])
  ++ "\n"
];