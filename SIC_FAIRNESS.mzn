%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SIC OPTIMISATION
%
% SSU:
%   distribute fairly within each doctor's min/max range
%
% INCHARGE:
%   distribute fairly within each doctor's min/max range
%
% ONCALL:
%   prefer 2 or 3
%   discourage 1
%   strongly discourage 0 if doctor is eligible for OC
%   discourage 4 or 5
%
% Existing min/max and eligibility constraints remain HARD.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SSU FAIRNESS
%
% Desired value is the midpoint between:
%
%       min_s[d] and target_s[d]
%
% We multiply by 2 to avoid floating point arithmetic.
%
% Example:
%
%       allowed S = 1..4
%
% midpoint = 2.5
%
%       2*n_s - (1+4)
%
% is -1 at n_s=2 and +1 at n_s=3.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

array[docs] of var -2*DAYS..2*DAYS: dev_s;
array[docs] of var 0..2*DAYS: abs_dev_s;

constraint forall(d in docs)(
    dev_s[d] =
        2 * n_s[d] - (min_s[d] + target_s[d])
);

constraint forall(d in docs)(
    abs_dev_s[d] = abs(dev_s[d])
);


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% INCHARGE FAIRNESS
%
% Same principle as SSU.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

array[docs] of var -2*DAYS..2*DAYS: dev_i;
array[docs] of var 0..2*DAYS: abs_dev_i;

constraint forall(d in docs)(
    dev_i[d] =
        2 * n_i[d] - (min_i[d] + target_i[d])
);

constraint forall(d in docs)(
    abs_dev_i[d] = abs(dev_i[d])
);


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% COMBINED SSU + INCHARGE FAIRNESS COST
%
% Lower is better.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

var 0..(4 * card(docs) * DAYS): si_fairness_cost;

constraint
    si_fairness_cost =
        sum(d in docs)(
              abs_dev_s[d]
            + abs_dev_i[d]
        );


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ONCALL PREFERENCE
%
% Assumes maximum OC is 5.
%
% Number of OC      Penalty
%
%       0              20
%       1               5
%       2               0
%       3               0
%       4               3
%       5               8
%
% Therefore:
%
%       2 or 3 = ideal
%       1      = undesirable
%       0      = strongly undesirable
%       4      = acceptable but less desirable
%       5      = considerably less desirable
%
% A doctor with target_oc[d] = 0 is excluded from this
% optimisation cost completely.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

array[0..5] of int: OC_PENALTY =
    array1d(
        0..5,
        [20, 5, 0, 0, 3, 8]
    );


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TOTAL ONCALL COST
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

var 0..(20 * card(docs)): oc_cost;

constraint
    oc_cost =
        sum(
            d in docs
            where target_oc[d] > 0
        )(
            OC_PENALTY[n_oc[d]]
        );


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TOTAL OPTIMISATION COST
%
% OC is deliberately weighted more heavily than the
% fine-tuning of S and I.
%
% Consequently the solver will strongly try to avoid leaving
% an OC-eligible doctor on zero when a better redistribution
% is possible.
%
% Once OC is reasonably distributed, S and I fairness helps
% choose between those solutions.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

var 0..(
      200 * card(docs)
    + 4 * card(docs) * DAYS
):
    optimisation_cost;

constraint
    optimisation_cost =
          10 * oc_cost
        + si_fairness_cost;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SOLVE
%
% THIS SHOULD BE THE ONLY SOLVE STATEMENT IN THE MODEL.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

solve minimize optimisation_cost;


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DIAGNOSTIC OUTPUT
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

output [
    "\nOPTIMISATION\n",
    "----------------------------------------\n",
    "OC cost           = " ++ show(oc_cost) ++ "\n",
    "S/I fairness cost = " ++ show(si_fairness_cost) ++ "\n",
    "Total cost        = " ++ show(optimisation_cost) ++ "\n",
    "----------------------------------------\n\n"
];

/*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% OPTIONAL: SHOW EACH DOCTOR'S OC PENALTY
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

output [
    show(d)
    ++ "\tOC = "
    ++ show(n_oc[d])
    ++
    if fix(target_oc[d]) > 0 then
        "\tOC penalty = "
        ++ show(OC_PENALTY[n_oc[d]])
    else
        "\tOC not eligible"
    endif
    ++ "\n"
    | d in docs
];


*/