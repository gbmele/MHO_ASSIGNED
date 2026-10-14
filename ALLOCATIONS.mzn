%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DEPARTMENTAL ALLOCATION LAYER
%
% roster / R describes the underlying roster state
% alloc describes the actual departmental allocation
%
% ROSTER STATES USED HERE
%
%   a   = rostered AM
%   p   = rostered PM
%   c   = rostered C
%
%   o   = open / available
%
%   ap  = may be allocated AM or PM, or remain unallocated
%
%   u   = completely unavailable
%   ua  = unavailable AM
%   up  = unavailable PM
%
%
% ALLOCATION STATES
%
%   AM
%   PM
%   C
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
set of int: days = 1..DAYS;


enum ALLOC = { AM, PM, C };
array[docs,days,ALLOC] of var 0..1: alloc;



set of docs: debug_docs={gmele,avarma,ccobela,awallac};

%constraint forall(doc in docs, day in days, sh in shifts) (
%  if doc in debug_docs then
%    R[doc,day,o] = 1
%  else
%    R[doc,day,sh] = bool2int(roster[doc,day,sh])
%  endif
%);
array[docs,days,shifts] of var 0..1: R;

constraint forall(
    doc in docs,
    day in days,
    sh in shifts
    where sh != u
)(
    R[doc,day,sh] =
        bool2int(roster[doc,day,sh])
);
%%account for leave
constraint forall(doc in docs, day in days) (
    R[doc,day,u] =
        bool2int(
            roster[doc,day,u]
            \/
            roster[doc,day,l]
        )
);


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% DEBUG DOCS


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ONE ALLOCATION PER DOCTOR PER DAY
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
constraint forall(doc in docs, day in days)(
      alloc[doc,day,AM]
    + alloc[doc,day,PM]
    + alloc[doc,day,C]
    <= 1
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% CHANNEL ROSTER -> ALLOCATION
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% CHANNEL R -> ALLOCATION
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint forall(doc in docs, day in days)(

    % ----------------------------------------------------------
    % A
    % ----------------------------------------------------------

    R[doc,day,a] <= alloc[doc,day,AM]

    /\

    alloc[doc,day,AM]
      <= R[doc,day,a]
       + R[doc,day,o]
       + R[doc,day,ap]
       + R[doc,day,ao]


    % ----------------------------------------------------------
    % P
    % ----------------------------------------------------------

    /\

    R[doc,day,p] <= alloc[doc,day,PM]

    /\

    alloc[doc,day,PM]
      <= R[doc,day,p]
       + R[doc,day,o]
       + R[doc,day,ap]
       + R[doc,day,po]


    % ----------------------------------------------------------
    % C
    % ----------------------------------------------------------

    /\

    R[doc,day,c] <= alloc[doc,day,C]

    /\

    alloc[doc,day,C]
      <= R[doc,day,c]
       + R[doc,day,o]

);



/*
constraint forall(doc in docs, day in days)(
    R[doc,day,a] <= alloc[doc,day,AM]
    /\
    alloc[doc,day,AM] <= R[doc,day,a] + R[doc,day,o] + R[doc,day,ap]
    /\
    R[doc,day,p] <= alloc[doc,day,PM]
    /\
    alloc[doc,day,PM] <= R[doc,day,p] + R[doc,day,o] + R[doc,day,ap]
    /\
    R[doc,day,c] <= alloc[doc,day,C]
    /\
    alloc[doc,day,C] <= R[doc,day,c]
);
*/
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% UNAVAILABILITY CHANNELING
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
constraint forall(doc in docs, day in days)(
      R[doc,day,u]
    + alloc[doc,day,AM]
    + alloc[doc,day,PM]
    + alloc[doc,day,C]
    <= 1
    /\
      R[doc,day,ua] + alloc[doc,day,AM] <= 1
    /\
      R[doc,day,up] + alloc[doc,day,PM] <= 1
);





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TOTAL COUNTS BY DOCTOR
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
array[docs] of var 0..DAYS: n_am;
array[docs] of var 0..DAYS: n_pm;
array[docs] of var 0..DAYS: n_c;

constraint forall(doc in docs)(
    n_am[doc] = sum(day in days)(alloc[doc,day,AM])
    /\
    n_pm[doc] = sum(day in days)(alloc[doc,day,PM])
    /\
    n_c[doc] = sum(day in days)(alloc[doc,day,C])
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PM COUNTS BY WEEKDAY
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
array[docs] of var 0..DAYS: n_mon_pm;
array[docs] of var 0..DAYS: n_tue_pm;
array[docs] of var 0..DAYS: n_wed_pm;
array[docs] of var 0..DAYS: n_thu_pm;
array[docs] of var 0..DAYS: n_fri_pm;

constraint forall(doc in docs)(
    n_mon_pm[doc] = sum(day in days where day mod 7 = 1)(alloc[doc,day,PM])
    /\
    n_tue_pm[doc] = sum(day in days where day mod 7 = 2)(alloc[doc,day,PM])
    /\
    n_wed_pm[doc] = sum(day in days where day mod 7 = 3)(alloc[doc,day,PM])
    /\
    n_thu_pm[doc] = sum(day in days where day mod 7 = 4)(alloc[doc,day,PM])
    /\
    n_fri_pm[doc] = sum(day in days where day mod 7 = 5)(alloc[doc,day,PM])
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% WEEKEND COUNTS BY DOCTOR
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
array[docs] of var 0..DAYS: n_sat_am;
array[docs] of var 0..DAYS: n_sat_pm;
array[docs] of var 0..DAYS: n_sun_am;
array[docs] of var 0..DAYS: n_sun_pm;

constraint forall(doc in docs)(
    n_sat_am[doc] = sum(day in days where day mod 7 = 6)(alloc[doc,day,AM])
    /\
    n_sat_pm[doc] = sum(day in days where day mod 7 = 6)(alloc[doc,day,PM])
    /\
    n_sun_am[doc] = sum(day in days where day mod 7 = 0)(alloc[doc,day,AM])
    /\
    n_sun_pm[doc] = sum(day in days where day mod 7 = 0)(alloc[doc,day,PM])
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% COVERAGE PARAMETERS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
int: mon_am_min=3; int: mon_am_max=16;
int: mon_pm_min=3; int: mon_pm_max=6;
int: mon_c_min=0;  int: mon_c_max=10;

int: tue_am_min=3; int: tue_am_max=16;
int: tue_pm_min=3; int: tue_pm_max=16;
int: tue_c_min=0;  int: tue_c_max=10;

int: wed_am_min=3; int: wed_am_max=16;
int: wed_pm_min=3; int: wed_pm_max=16;
int: wed_c_min=0;  int: wed_c_max=10;

int: thu_am_min=3; int: thu_am_max=16;
int: thu_pm_min=3; int: thu_pm_max=16;
int: thu_c_min=0;  int: thu_c_max=10;

int: fri_am_min=3; int: fri_am_max=16;
int: fri_pm_min=3; int: fri_pm_max=16;
int: fri_c_min=0;  int: fri_c_max=10;

int: sat_am_min=3; int: sat_am_max=16;
int: sat_pm_min=3; int: sat_pm_max=16;

int: sun_am_min=3; int: sun_am_max=16;
int: sun_pm_min=3; int: sun_pm_max=16;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% MONDAY COVERAGE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
constraint forall(day in days where day mod 7 = 1)(
    sum(doc in docs)(alloc[doc,day,AM]) >= mon_am_min /\
    sum(doc in docs)(alloc[doc,day,AM]) <= mon_am_max /\
    sum(doc in docs)(alloc[doc,day,PM]) >= mon_pm_min /\
    sum(doc in docs)(alloc[doc,day,PM]) <= mon_pm_max /\
    sum(doc in docs)(alloc[doc,day,C])  >= mon_c_min /\
    sum(doc in docs)(alloc[doc,day,C])  <= mon_c_max
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TUESDAY COVERAGE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
constraint forall(day in days where day mod 7 = 2)(
    sum(doc in docs)(alloc[doc,day,AM]) >= tue_am_min /\
    sum(doc in docs)(alloc[doc,day,AM]) <= tue_am_max /\
    sum(doc in docs)(alloc[doc,day,PM]) >= tue_pm_min /\
    sum(doc in docs)(alloc[doc,day,PM]) <= tue_pm_max /\
    sum(doc in docs)(alloc[doc,day,C])  >= tue_c_min /\
    sum(doc in docs)(alloc[doc,day,C])  <= tue_c_max
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% WEDNESDAY COVERAGE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
constraint forall(day in days where day mod 7 = 3)(
    sum(doc in docs)(alloc[doc,day,AM]) >= wed_am_min /\
    sum(doc in docs)(alloc[doc,day,AM]) <= wed_am_max /\
    sum(doc in docs)(alloc[doc,day,PM]) >= wed_pm_min /\
    sum(doc in docs)(alloc[doc,day,PM]) <= wed_pm_max /\
    sum(doc in docs)(alloc[doc,day,C])  >= wed_c_min /\
    sum(doc in docs)(alloc[doc,day,C])  <= wed_c_max
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% THURSDAY COVERAGE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
constraint forall(day in days where day mod 7 = 4)(
    sum(doc in docs)(alloc[doc,day,AM]) >= thu_am_min /\
    sum(doc in docs)(alloc[doc,day,AM]) <= thu_am_max /\
    sum(doc in docs)(alloc[doc,day,PM]) >= thu_pm_min /\
    sum(doc in docs)(alloc[doc,day,PM]) <= thu_pm_max /\
    sum(doc in docs)(alloc[doc,day,C])  >= thu_c_min /\
    sum(doc in docs)(alloc[doc,day,C])  <= thu_c_max
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% FRIDAY COVERAGE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
constraint forall(day in days where day mod 7 = 5)(
    sum(doc in docs)(alloc[doc,day,AM]) >= fri_am_min /\
    sum(doc in docs)(alloc[doc,day,AM]) <= fri_am_max /\
    sum(doc in docs)(alloc[doc,day,PM]) >= fri_pm_min /\
    sum(doc in docs)(alloc[doc,day,PM]) <= fri_pm_max /\
    sum(doc in docs)(alloc[doc,day,C])  >= fri_c_min /\
    sum(doc in docs)(alloc[doc,day,C])  <= fri_c_max
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SATURDAY COVERAGE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
constraint forall(day in days where day mod 7 = 6)(
    sum(doc in docs)(alloc[doc,day,AM]) >= sat_am_min /\
    sum(doc in docs)(alloc[doc,day,AM]) <= sat_am_max /\
    sum(doc in docs)(alloc[doc,day,PM]) >= sat_pm_min /\
    sum(doc in docs)(alloc[doc,day,PM]) <= sat_pm_max
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SUNDAY COVERAGE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
constraint forall(day in days where day mod 7 = 0)(
    sum(doc in docs)(alloc[doc,day,AM]) >= sun_am_min /\
    sum(doc in docs)(alloc[doc,day,AM]) <= sun_am_max /\
    sum(doc in docs)(alloc[doc,day,PM]) >= sun_pm_min /\
    sum(doc in docs)(alloc[doc,day,PM]) <= sun_pm_max
);



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PREVENT C ALLOCATION ON WEEKENDS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
constraint forall(
    doc in docs,
    day in days
    where day mod 7 = 6 \/ day mod 7 = 0
)(
    alloc[doc,day,C] = 0
);






%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% GENERIC WEEKLY ALLOCATION TEMPLATE
%
% Example:
%
% array[1..7] of shifts: greg_template =
% [c,p,o,c,ao,ao,ao];
%
%  then use constraint alloc_template(doc,greg_template);
%
% Meaning:
%
% a = AM
% p = PM
% c = C
% o = no departmental allocation
%
% ao = AM or no allocation
% po = PM or no allocation
% apo = AM or PM or no allocation
%
% u = no allocation
% ua = unavailable AM:
% PM or C may still be possible subject to other rules
% up = unavailable PM:
% AM or C may still be possible subject to other rules
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
 
predicate alloc_template(
docs: doc,
array[1..7] of shifts: template
) =
 
forall(
monday in days
where monday mod 7 = 1
/\ monday + 6 <= max(days),
d in 1..7
) (
 
let {
int: day = monday + d - 1
} in
 
% ==========================================================
% a = compulsory AM
% ==========================================================
if template[d] = a then
 
alloc[doc,day,AM] = 1
/\
alloc[doc,day,PM] = 0
/\
alloc[doc,day,C] = 0
 
 
% ==========================================================
% p = compulsory PM
% ==========================================================
elseif template[d] = p then
 
alloc[doc,day,AM] = 0
/\
alloc[doc,day,PM] = 1
/\
alloc[doc,day,C] = 0
 
 
% ==========================================================
% c = compulsory C
% ==========================================================
elseif template[d] = c then
 
alloc[doc,day,AM] = 0
/\
alloc[doc,day,PM] = 0
/\
alloc[doc,day,C] = 1
 
 
% ==========================================================
% o = no departmental allocation
% ==========================================================
elseif template[d] = o then
 
alloc[doc,day,AM] = 0
/\
alloc[doc,day,PM] = 0
/\
alloc[doc,day,C] = 0
 
 
% ==========================================================
% ao = AM OR no allocation
% ==========================================================
elseif template[d] = ao then
 
alloc[doc,day,PM] = 0
/\
alloc[doc,day,C] = 0
 
 
% ==========================================================
% po = PM OR no allocation
% ==========================================================
elseif template[d] = po then
 
alloc[doc,day,AM] = 0
/\
alloc[doc,day,C] = 0
 
 
% ==========================================================
% apo = AM OR PM OR no allocation
% ==========================================================
elseif template[d] = apo then
 
alloc[doc,day,C] = 0
 
 
% ==========================================================
% u = completely unavailable
% ==========================================================
elseif template[d] = u then
 
alloc[doc,day,AM] = 0
/\
alloc[doc,day,PM] = 0
/\
alloc[doc,day,C] = 0
 
 
% ==========================================================
% ua = unavailable AM
%
% Only prohibit AM here.
% Other allocation/channeling rules determine whether
% PM or C is possible.
% ==========================================================
elseif template[d] = ua then
 
alloc[doc,day,AM] = 0
 
 
% ==========================================================
% up = unavailable PM
%
% Only prohibit PM here.
% Other allocation/channeling rules determine whether
% AM or C is possible.
% ==========================================================
elseif template[d] = up then
 
alloc[doc,day,PM] = 0
 
 
else
false
endif
);

% END ALLOCATE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


predicate four_shifts_week(docs: doc) =
forall(day in days where day mod 7 = 1 /\ day + 6 <= max(days)) 
  
  (sum(d in day..day+6, sh in ALLOC)(alloc[doc,d,sh]) = 4);

predicate three_shifts_week(docs: doc) =
forall(day in days where day mod 7 = 1 /\ day + 6 <= max(days)) 
  
  (sum(d in day..day+6, sh in ALLOC)(alloc[doc,d,sh]) = 3);
  
  
%% just apc count mon-fri  
predicate ap(docs:doc,int:A,int:P)=
  apc(doc,A,P,0);


predicate apc(docs: doc, int: A, int: P, int: Cn) =
  forall(day in days where day mod 7 = 1 /\ day + 4 <= max(days)) (
 
      sum(d in day..day+4)( alloc[doc,d,AM]) = A /\
      
      sum(d in day..day+4)( alloc[doc,d,PM]) = P /\
      
      sum(d in day..day+4)(alloc[doc,d,C])   = Cn);  


%% set ps per weekday
predicate p_per_week(docs: doc, int: P) =
forall(mon in days where mon mod 7 = 1 /\ mon + 4 <= max(days)) 
   (sum(d in mon..mon+4)(alloc[doc,d,PM]) = P);

%% set C per weekday
predicate c_per_week(docs: doc, int: Cn) =
forall(mon in days where mon mod 7 = 1 /\ mon + 4 <= max(days)) 
   (sum(d in mon..mon+4)(alloc[doc,d,C]) = Cn);


%11111111111111111111111111111111111111111111111111111111111111111111111111111111111111
%11111111111111111111111111111111111111111111111111111111111111111111111111111111111111
%% now WEEKENDS
predicate no_split_weekends(docs: doc) =
forall(day in days where day mod 7 = 6 /\ day < max(days)) (

  alloc[doc,day,AM] = alloc[doc,day+1,AM] /\
  alloc[doc,day,PM] = alloc[doc,day+1,PM]);

%%only one for the weekend
predicate split_weekends(docs: doc) =
forall(day in days where day mod 7 = 6 /\ day < max(days)) (
     
      alloc[doc,day,AM]
    + alloc[doc,day,PM]
    + alloc[doc,day+1,AM]
    + alloc[doc,day+1,PM]
    <= 1);

%%no consec full weekends for fulltimers really----
predicate no_consec_weekends(docs: doc) =
forall(day in days where day mod 7 = 6 /\ day + 8 <= max(days)) (
 
          alloc[doc,day,AM]
        + alloc[doc,day,PM]
        + alloc[doc,day+1,AM]
        + alloc[doc,day+1,PM]  +
 
        alloc[doc,day+7,AM]
      + alloc[doc,day+7,PM]
      + alloc[doc,day+8,AM]
      + alloc[doc,day+8,PM]
 
<= 2);

predicate assign_weekends(docs:doc ,int:sat_a,int:sat_p,int:sun_a,int:sun_p)=
          (n_sat_am[doc]=sat_a /\
           n_sat_pm[doc]=sat_p /\
           n_sun_am[doc]=sun_a /\
           n_sun_pm[doc]=sun_p);




%%END WEEKENDS
%%%MORE FULLTIMER STUFF


%% for fulltimers - a full weekend (any shift) takes an AM from each of the weeks
predicate weekend_for_am(docs: doc, int: A) =
forall(mon in days where mon mod 7 = 1 /\ mon + 13 <= max(days) /\ ((mon - 1) div 7) mod 2 = 0) (
 
let {
var int: weekend_shifts =
alloc[doc,mon+5,AM]
+ alloc[doc,mon+5,PM]
+ alloc[doc,mon+6,AM]
+ alloc[doc,mon+6,PM]
+ alloc[doc,mon+12,AM]
+ alloc[doc,mon+12,PM]
+ alloc[doc,mon+13,AM]
+ alloc[doc,mon+13,PM]
} in
 
% If there is a full weekend (= 2 shifts),
% remove one weekday AM from EACH week.
sum(d in mon..mon+4)(alloc[doc,d,AM]) = A - weekend_shifts div 2
 
/\
 
sum(d in mon+7..mon+11)(alloc[doc,d,AM]) = A - weekend_shifts div 2
);


predicate shifts_per_fortnight(docs: doc, int: N) =
forall(mon in days where mon mod 7 = 1 /\ mon + 13 <= max(days)/\ ((mon - 1) div 7) mod 2 = 0) 
(sum(d in mon..mon+13, sh in ALLOC)( alloc[doc,d,sh]) = N);

predicate shifts_per_fortnight_la(docs: doc, int: N) =

  forall(mon in days
         where mon mod 7 = 1
           /\ mon + 13 <= max(days)
           /\ ((mon - 1) div 7) mod 2 = 0)

  (

    let {

      var int: leave_weeks =

          bool2int(
            sum(d in mon..mon+6)
              (bool2int(roster[doc,d,l]))
            = 7
          )

        +

          bool2int(
            sum(d in mon+7..mon+13)
              (bool2int(roster[doc,d,l]))
            = 7
          );

    } in

      sum(d in mon..mon+13, sh in ALLOC)
        (alloc[doc,d,sh])

      =

      N * (2 - leave_weeks) div 2

  );

predicate balanced_fortnight(docs: doc) =

  forall(mon in days
         where mon mod 7 = 1
           /\ mon + 13 <= max(days)
           /\ ((mon - 1) div 7) mod 2 = 0)

  (

    let {

      var int: week1 =
          sum(d in mon..mon+6, sh in ALLOC)
              (alloc[doc,d,sh]);

      var int: week2 =
          sum(d in mon+7..mon+13, sh in ALLOC)
              (alloc[doc,d,sh]);

    } in

      week1 in 3..5

      /\

      week2 in 3..5

  );



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 14-DAY ALLOCATION TEMPLATE
%
% Positions:
%
% 1..7 = Week 1 Mon-Sun
% 8..14 = Week 2 Mon-Sun
%
% Template meanings:
%
% a = AM compulsory
% p = PM compulsory
% c = C compulsory
% o = no departmental allocation
%
% ao = AM or no allocation
% po = PM or no allocation
% apo = AM or PM or no allocation
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
%%
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% EXAMPLE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
%%array[1..14] of shifts: greg_template =
%%[
%% WEEK 1
%%ao, ao, ao, po, o, apo, apo,
 
%% WEEK 2
%%ao, ao, ao, po, o, apo, apo
%%];
 
%%constraint alloc_template14(gmele, greg_template);

predicate alloc_template14(docs: doc, array[1..14] of shifts: template) =
 
forall(
mon in days
where mon mod 7 = 1
/\ mon + 13 <= max(days)
/\ ((mon - 1) div 7) mod 2 = 0,
d in 1..14
) (
 
let {
int: day = mon + d - 1
} in
 
% A = compulsory AM
if template[d] = a then
 
alloc[doc,day,AM] = 1
/\
alloc[doc,day,PM] = 0
/\
alloc[doc,day,C] = 0
 
 
% P = compulsory PM
elseif template[d] = p then
 
alloc[doc,day,AM] = 0
/\
alloc[doc,day,PM] = 1
/\
alloc[doc,day,C] = 0
 
 
% C = compulsory C
elseif template[d] = c then
 
alloc[doc,day,AM] = 0
/\
alloc[doc,day,PM] = 0
/\
alloc[doc,day,C] = 1
 
 
% O = no departmental allocation
elseif template[d] = o then
 
alloc[doc,day,AM] = 0
/\
alloc[doc,day,PM] = 0
/\
alloc[doc,day,C] = 0
 
 
% AO = AM or unallocated
elseif template[d] = ao then
 
alloc[doc,day,PM] = 0
/\
alloc[doc,day,C] = 0
 
 
% PO = PM or unallocated
elseif template[d] = po then
 
alloc[doc,day,AM] = 0
/\
alloc[doc,day,C] = 0
 
 
% APO = AM, PM or unallocated
elseif template[d] = apo then
 
alloc[doc,day,C] = 0
 
 
% U = completely unavailable
elseif template[d] = u then
 
alloc[doc,day,AM] = 0
/\
alloc[doc,day,PM] = 0
/\
alloc[doc,day,C] = 0
 
 
% UA = unavailable AM
elseif template[d] = ua then
 
alloc[doc,day,AM] = 0
 
 
% UP = unavailable PM
elseif template[d] = up then
 
alloc[doc,day,PM] = 0
 
elseif template[d] = oc then

    alloc[doc,day,AM] = 0 /\
    alloc[doc,day,PM] = 0

elseif template[d] = co then

    alloc[doc,day,AM] = 0 /\
    alloc[doc,day,PM] = 0

elseif template[d] = aco then

    alloc[doc,day,PM] = 0

elseif template[d] = apoc then

    true
    
    
else
    assert(false, "Unknown template state")
 
endif
);



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%code for all docs
%% all docs no am after pm from an allocation point of view

predicate no_am_after_pm() =
  forall(doc in docs, day in days where day < max(days)) 
    (alloc[doc,day,PM] + alloc[doc,day+1,AM] <= 1);

constraint no_am_after_pm();

predicate no_monday_after_sunday(docs: doc) =
    forall(day in days
           where day mod 7 = 0
             /\ day < max(days)) (

        alloc[doc,day,AM]
      + alloc[doc,day,PM]
      + alloc[doc,day+1,AM]
      + alloc[doc,day+1,PM]
        <= 1
    );
predicate no_friday_before_saturday(docs: doc) =

    forall(day in days
           where day mod 7 = 5
             /\ day < max(days)) (

        alloc[doc,day,AM]
      + alloc[doc,day,PM]
      + alloc[doc,day+1,AM]
      + alloc[doc,day+1,PM]

        <= 1
    );
predicate no_saturday_after_friday(docs: doc) =
    forall(day in days
           where day mod 7 = 5
             /\ day < max(days)) (

        alloc[doc,day,AM]
      + alloc[doc,day,PM]
      + alloc[doc,day+1,AM]
      + alloc[doc,day+1,PM]
        <= 1
    );

predicate no_weekend_before_leave(docs: doc) =
  forall(day in days where day mod 7 = 6 /\ day + 2 <= max(days))
    (
      (alloc[doc,day,AM]
       + alloc[doc,day,PM]
       + alloc[doc,day+1,AM]
       + alloc[doc,day+1,PM]
       >= 1)
      ->
      not roster[doc,day+2,l]
    );

predicate no_three_pms(docs: doc) =
  forall(day in days where day + 2 <= max(days))
    (
      alloc[doc,day,PM]
    + alloc[doc,day+1,PM]
    + alloc[doc,day+2,PM]
    <= 2
    );

predicate no_four_ams(docs: doc) =
  forall(day in days where day + 3 <= max(days))
    (
      alloc[doc,day,AM]
    + alloc[doc,day+1,AM]
    + alloc[doc,day+2,AM]
    + alloc[doc,day+3,AM]
    
    <= 3
    );


%%%%%%                                      
                                                                                            
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% STRUCTURAL SUMMARY
%
% roster / R
%     |
%     v
% CHANNEL
%     |
%     v
% alloc[doc,day,AM/PM/C]
%     |
%     +---- coverage DOWN across doctors
%     |
%     +---- counts ACROSS days for each doctor
%     |
%     +---- patterns
%     |
%     +---- exceptions
%     |
%     +---- optimisation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%TESTDOC
%% TESTDOC is one doc in enum for testing purposes
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

include "ALLOCATIONS_MH.mzn";

predicate test_amrita(docs:D) =
  (alloc_template14(D,[apoc,apoc,apoc,apoc,apo,apo,apo,
                            apoc,apoc,apoc,apoc,apo,apo,apo]) /\
                  
                   leave_weeks(D,{})     /\
                   shifts_per_fortnight(D,6) /\
                   c_per_week_la(D,1) /\ p_per_week_la(D,1) /\ a_per_week_range_la(D,0,1)  /\
                   assign_weekends(D,1,1,1,1) /\
                   no_split_weekends(D) /\ no_consec_weekends(D) /\
                   %no_weekend_before_leave(D) /\
                   n_fri_pm[D] in 2..2        /\
                   no_three_pms(D));

predicate test_greg_nathan(docs:D) =
  (alloc_template14(D,[po,o,po,co,o,po,o,
                       po,o,po,co,o,po,o])    /\
                   c_per_week_la(D,1)  /\ 
                   p_per_week_la(D,2)   /\
                   every_saturday(D));
                   
predicate test_martin_lew(docs:D) =
  (alloc_template14(D,[o,o,ao,ao,o,o,apo,
                       o,o,ao,ao,o,o,apo])    /\
                   a_per_week_range_la(D,2,2) /\
                   leave_days(D,{})           /\
                    every_sunday(D)           %%every sunday is must work every sunday and this is leave aware
); 

predicate test_teresa(docs:D) =
  (alloc_template14(D,[apo,ao,co,apo,apo,apo,apo,
                             apo,ao,co,apo,apo,apo,apo]) /\
                  
                   leave_weeks(TESTDOC,{D})     /\
                   apc_per_week_la(D,1,1,1) /\
                   assign_weekends(D,1,1,1,1) /\
                   no_split_weekends(D) /\ no_consec_weekends(D) /\
                   no_weekend_before_leave(D) /\
                   n_fri_pm[D] in 2..3 /\
                   no_three_pms(D));

                   
predicate test_brendon(docs:D) =
  (alloc_template14(D,[o,o,o,po,o,po,o,
                             o,o,o,po,o,po,o]) /\
                   shifts_per_week_la(D,1)
   );

predicate test_rm(docs:D) =
    (alloc_template14(D,[ao,apo,co,ao,apo,ao,ao,
                               ao,apo,co,ao,apo,ao,ao]) /\
 
    leave_weeks(D,{})  /\
    shifts_per_fortnight_la(D,8) /\
    assign_weekends(D,2,0,2,0) /\
    no_split_weekends(D) /\ 
    no_consec_weekends(D) /\
    no_monday_after_sunday(D) /\
    no_friday_before_saturday(D) /\
    p_per_week_la(D,1) /\   
    c_per_week_la(D,1) /\
    a_per_week_range_la(D,1,2) /\
    n_fri_pm[D]=2
    );
 
%% min fulltiemr splits weekends intially hard now good 2a1pic
predicate test_min() =
    (alloc_template14(TESTDOC,[ao,ao,apo,co,apo,apo,apo,
                               ao,ao,apo,co,apo,apo,apo]) /\
 
    leave_weeks(TESTDOC,{})  /\
    shifts_per_fortnight_la(TESTDOC,8) /\
    assign_weekends(TESTDOC,1,1,1,1) /\
    split_weekends(TESTDOC) /\ 
    no_monday_after_sunday(TESTDOC) /\
    p_per_week_la(TESTDOC,1) /\
    c_per_week_la(TESTDOC,1) /\
    a_per_week_range_la(TESTDOC,1,2) /\
    n_fri_pm[TESTDOC]=2
    );

%%cc and db really 3a1p0c
predicate test_cc() =
    (alloc_template14(TESTDOC,[apo,ao,ao,ao,apo,apo,apo,
                               apo,ao,ao,ao,apo,apo,apo]) /\
 
    leave_weeks(TESTDOC,{5,8})  /\
    shifts_per_fortnight_la(TESTDOC,8) /\
    assign_weekends(TESTDOC,1,1,1,1) /\
    no_split_weekends(TESTDOC) /\ 
    no_four_ams(TESTDOC) /\
    no_monday_after_sunday(TESTDOC) /\
    p_per_week_la(TESTDOC,1) /\
    c_per_week_la(TESTDOC,0) /\
    a_per_week_range_la(TESTDOC,2,3) /\
    n_fri_pm[TESTDOC]=2  /\
    no_weekend_before_leave(TESTDOC)
    );

predicate test_db() =
    (alloc_template14(TESTDOC,[ao,apo,ao,ao,apo,apo,apo,
                               ao,apo,ao,ao,apo,apo,apo]) /\
 
    leave_weeks(TESTDOC,{2,3})  /\
    shifts_per_fortnight_la(TESTDOC,8) /\
    assign_weekends(TESTDOC,2,0,2,0) /\
    no_split_weekends(TESTDOC) /\ 
    no_monday_after_sunday(TESTDOC) /\
    no_four_ams(TESTDOC)  /\
    p_per_week_la(TESTDOC,1) /\
    c_per_week_la(TESTDOC,0) /\
    a_per_week_range_la(TESTDOC,2,3) /\
    n_fri_pm[TESTDOC]=2  /\
    no_weekend_before_leave(TESTDOC)
    );


predicate test_gm() =
    (alloc_template14(TESTDOC,[co,po,o,co,ao,ao,ao,
                               co,po,o,co,ao,ao,ao]) /\
 
    leave_weeks(TESTDOC,{1,2,3})  /\
    shifts_per_fortnight_la(TESTDOC,8) /\
    assign_weekends(TESTDOC,2,0,2,0) /\
    split_weekends(TESTDOC) /\ 
    p_per_week_la(TESTDOC,1) /\
    c_per_week_la(TESTDOC,2) /\
    a_per_week_range_la(TESTDOC,0,1) /\
    no_weekend_before_leave(TESTDOC)
    );

predicate test_jlim() =
    (alloc_template14(TESTDOC,[o,ao,co,ao,o,apo,apo,
                               o,po,co,po,o,apo,apo]) /\
 
    leave_weeks(TESTDOC,{})  /\
    shifts_per_fortnight_la(TESTDOC,6) /\
    c_per_week_la(TESTDOC,1)  /\
    assign_weekends(TESTDOC,1,1,1,1) /\
    no_split_weekends(TESTDOC) /\
    no_split_weekends(TESTDOC)
    );


predicate test_dl() =
    (alloc_template14(TESTDOC,[ao,apo,co,ao,apo,apo,apo,
                               ao,apo,co,ao,apo,apo,apo]) /\
 
    leave_weeks(TESTDOC,{3,4})  /\
    shifts_per_fortnight_la(TESTDOC,8) /\
    assign_weekends(TESTDOC,2,0,2,0) /\
    no_split_weekends(TESTDOC) /\ 
    no_consec_weekends(TESTDOC) /\
    no_monday_after_sunday(TESTDOC) /\
    p_per_week_la(TESTDOC,1) /\
    c_per_week_la(TESTDOC,1) /\
    a_per_week_range_la(TESTDOC,1,2) /\
    n_fri_pm[TESTDOC]=2
    );

predicate test_ck() =
    (alloc_template14(TESTDOC,[apo,apo,apo,o,apo,apo,apo,
                               apo,apo,apo,o,apo,apo,apo]) /\
 
    shifts_per_fortnight(TESTDOC,7) /\
    leave_weeks(TESTDOC,{})  /\
    no_split_weekends(TESTDOC) /\ 
    %no_monday_after_sunday(TESTDOC) /\
    no_three_pms(TESTDOC) /\
    no_four_ams(TESTDOC)  /\
    n_sat_am[TESTDOC]=3 /\ n_sat_pm[TESTDOC]=3
    );

predicate test_kimson() =
    (alloc_template14(TESTDOC,[po,po,co,po,po,po,po,
                               o,o,o,o,o,o,o]) /\
    leave_days(TESTDOC,{}) /\
    shifts_per_fortnight(TESTDOC,4) /\
    (forall(d in days where d mod 14 = 3) (roster[TESTDOC,d,l] =0  -> alloc[TESTDOC,d,C] = 1))  /\
    no_split_weekends(TESTDOC) 
    );

predicate test_jannet() =
    (alloc_template14(TESTDOC,[o,o,o,o,o,o,o,
                               apo,apo,apo,apo,apo,apo,apo]) /\
    leave_days(TESTDOC,{}) /\
    shifts_per_fortnight(TESTDOC,4) /\
    no_split_weekends(TESTDOC) /\
    no_three_pms(TESTDOC)   /\ 
    no_four_ams(TESTDOC) 
    );

predicate test_sk() =
    (alloc_template14(TESTDOC,[ao,co,po,o,o,apo,apo,
                               ao,co,po,o,o,apo,apo]) /\
    shifts_per_fortnight_la(TESTDOC,6)  /\
    leave_weeks(TESTDOC,{2,6,7}) /\
    no_split_weekends(TESTDOC) /\
    assign_weekends(TESTDOC,1,1,1,1) /\
    no_split_weekends(TESTDOC)       /\
    %no_monday_after_sunday(TESTDOC)  /\
    c_per_week_la(TESTDOC,1)         /\
    p_per_week_la(TESTDOC,1)         /\
    a_per_week_range_la(TESTDOC,0,1) 
    %/\
    %forall(day in days where day mod 7 = 6 /\ day + 6 <= max(days))
    %( ( not roster[TESTDOC,day,l]
    %    /\
    %    alloc[TESTDOC,day+6,AM] + alloc[TESTDOC,day+6,PM] > 0    )
    %->
    %  (alloc[TESTDOC,day,AM] + alloc[TESTDOC,day,PM] = 0))
);

predicate test_damien() =
    (alloc_template14(TESTDOC,[o,o,ao,o,po,po,o,
                               o,o,ao,o,po,po,o]) /\
    leave_days(TESTDOC,{}) /\
    p_per_week_la(TESTDOC,1) /\
    a_per_week_range_la(TESTDOC,0,1) /\
    assign_weekends(TESTDOC,0,4,0,0) /\
    forall(day in days where day mod 7 = 6 /\ day + 7 <= max(days))
      ( alloc[TESTDOC,day,PM]  + alloc[TESTDOC,day+7,PM] <=1  /\ alloc[TESTDOC,day-3,AM] + alloc[TESTDOC,day,PM] <=1    ) /\
    shifts_per_fortnight(TESTDOC,4)
    );

predicate test_thu_or_sat() =
  %% good for yas
  (alloc_template14(TESTDOC,[o,o,o,apo,o,apo,o,
                             o,o,o,apo,o,apo,o]) /\
                   shifts_per_week_la(TESTDOC,1)   /\
                   n_sat_pm[TESTDOC] in 4..5        /\
                   leave_weeks(TESTDOC,{2,6}));


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%constraint test_amrita();
%constraint test_greg_nathan();
%constraint test_martin_lew(); 
%constraint test_teresa();
%constraint test_thu_or_sat();   %% yas essentially
%constraint test_brendon();
%constraint test_rm();
%constraint test_min();
%constraint test_cc();
%constraint test_gm();
%constraint test_db();
%constraint test_jlim();
%sconstraint test_dl();
%constraint test_ck();
%constraint test_kimson();
%constraint test_jannet();

%constraint test_sk();
%constraint test_damien();

%%include "ALLOCATIONS_MH.mzn";

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% leave type predicats for testing
%% use one or the other   cant use both in testing ONLY IN TESTING
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
predicate leave_days(docs: doc,set of int: leave_set) =
    (forall(day in leave_set)(roster[doc,day,l] = 1)
    /\
    forall(day in days diff leave_set)(roster[doc,day,o]=1))
;

/*                
predicate leave_weeks(docs: doc,set of int: weeks_off) =

    forall(day in days)(
        if ((day-1) div 7 + 1) in weeks_off then
            roster[doc,day,l] = 1
        else
            roster[doc,day,o] = 1
        endif
    );
*/
predicate leave_weeks(docs: doc,set of int: weeks_off) =

    forall(day in days where ((day-1) div 7 + 1) in weeks_off)(
        roster[doc,day,l] = 1
    );
    
%% leave aware code
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
predicate p_per_week_la(docs: doc, int: P) =

    forall(mon in days where mon mod 7 = 1 /\ mon + 4 <= max(days)) (
        sum(d in mon..mon+4)(alloc[doc,d,PM])
        = P * bool2int(sum(d in mon..mon+6)(bool2int(roster[doc,d,l])) < 7));

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
predicate c_per_week_la(docs: doc, int: Cn) =

    forall(mon in days where mon mod 7 = 1 /\ mon + 4 <= max(days)) (

        sum(d in mon..mon+4)(alloc[doc,d,C])

        = Cn * bool2int(sum(d in mon..mon+6)(bool2int(roster[doc,d,l])) < 7));

predicate a_per_week_la(docs: doc, int: An) =
  forall(mon in days where mon mod 7 = 1 /\ mon + 4 <= max(days))
    (
      sum(d in mon..mon+4)(alloc[doc,d,AM])
      =
      if sum(d in mon..mon+6)(bool2int(roster[doc,d,l])) = 7
      then 0
      else An
      endif
    );
predicate a_per_week_range_la(
    docs: doc,
    int: low,
    int: high
) =

  forall(mon in days
         where mon mod 7 = 1
           /\ mon + 6 <= max(days))

  (

    let {

      var int: leave_days =
        sum(d in mon..mon+6)
          (bool2int(roster[doc,d,l]));

      var int: weekday_AMs =
        sum(d in mon..mon+4)
          (alloc[doc,d,AM]);

    } in

      if leave_days = 7 then

        weekday_AMs = 0

      else

        weekday_AMs in low..high

      endif

  );

predicate apc_per_week_la(docs:doc,int:A,int:P,int:C)=
    a_per_week_la(doc,A) /\
    p_per_week_la(doc,P) /\
    c_per_week_la(doc,C);
    
predicate shifts_per_week_la(docs: doc, int: N) =
  forall(mon in days where mon mod 7 = 1 /\ mon + 6 <= max(days))
    (
      sum(d in mon..mon+6, sh in ALLOC)(alloc[doc,d,sh])
      =
      N * bool2int(
            sum(d in mon..mon+6)(bool2int(roster[doc,d,l])) < 7
          )
    );
    


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% FIXED WEEKEND SHIFTS
%
% Normal weekend:
%     shift allocated
%
% Leave weekend:
%     shift not allocated
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

predicate sat_am(docs: doc) =
  forall(day in days where day mod 7 = 6)
    (alloc[doc,day,AM] = bool2int(not roster[doc,day,l]));


%% eg greg nathans fixed pm == constraint sat_pm(greg_nathan)  -- converts the shift from the template to off when leave is allocated
predicate sat_pm(docs: doc) =
  forall(day in days where day mod 7 = 6)
    (alloc[doc,day,PM] = bool2int(not roster[doc,day,l]));

predicate sun_am(docs: doc) =
  forall(day in days where day mod 7 = 0)
    (alloc[doc,day,AM] = bool2int(not roster[doc,day,l]));

predicate sun_pm(docs: doc) =
  forall(day in days where day mod 7 = 0)
    (alloc[doc,day,PM] = bool2int(not roster[doc,day,l]));    

predicate every_saturday(docs: doc) =
  forall(day in days where day mod 7 = 6)
    (
      alloc[doc,day,AM]
    + alloc[doc,day,PM]
    =
      bool2int(not roster[doc,day,l])
    );

predicate every_sunday(docs: doc) =
  forall(day in days where day mod 7 = 0)
    (
      alloc[doc,day,AM]
    + alloc[doc,day,PM]
    =
      bool2int(not roster[doc,day,l])
    );

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% END LEAVE AWARE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% COVERAGE SHORTFALLS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

array[days] of var 0..10: am_shortfall;
array[days] of var 0..10: pm_shortfall;

constraint forall(day in days where day mod 7 = 1)(
    sum(doc in docs)(alloc[doc,day,AM])
    + am_shortfall[day]
    >= mon_am_min
);
constraint forall(day in days where day mod 7 = 1)(
    sum(doc in docs)(alloc[doc,day,PM])
    + pm_shortfall[day]
    >= mon_pm_min
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% TUESDAY SHORTFALLS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint forall(day in days where day mod 7 = 2)(
    sum(doc in docs)(alloc[doc,day,AM])
    + am_shortfall[day]
    >= tue_am_min
);

constraint forall(day in days where day mod 7 = 2)(
    sum(doc in docs)(alloc[doc,day,PM])
    + pm_shortfall[day]
    >= tue_pm_min
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% WEDNESDAY SHORTFALLS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint forall(day in days where day mod 7 = 3)(
    sum(doc in docs)(alloc[doc,day,AM])
    + am_shortfall[day]
    >= wed_am_min
);

constraint forall(day in days where day mod 7 = 3)(
    sum(doc in docs)(alloc[doc,day,PM])
    + pm_shortfall[day]
    >= wed_pm_min
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% THURSDAY SHORTFALLS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint forall(day in days where day mod 7 = 4)(
    sum(doc in docs)(alloc[doc,day,AM])
    + am_shortfall[day]
    >= thu_am_min
);

constraint forall(day in days where day mod 7 = 4)(
    sum(doc in docs)(alloc[doc,day,PM])
    + pm_shortfall[day]
    >= thu_pm_min
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% FRIDAY SHORTFALLS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint forall(day in days where day mod 7 = 5)(
    sum(doc in docs)(alloc[doc,day,AM])
    + am_shortfall[day]
    >= fri_am_min
);

constraint forall(day in days where day mod 7 = 5)(
    sum(doc in docs)(alloc[doc,day,PM])
    + pm_shortfall[day]
    >= fri_pm_min
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SATURDAY SHORTFALLS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint forall(day in days where day mod 7 = 6)(
    sum(doc in docs)(alloc[doc,day,AM])
    + am_shortfall[day]
    >= sat_am_min
);

constraint forall(day in days where day mod 7 = 6)(
    sum(doc in docs)(alloc[doc,day,PM])
    + pm_shortfall[day]
    >= sat_pm_min
);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SUNDAY SHORTFALLS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint forall(day in days where day mod 7 = 0)(
    sum(doc in docs)(alloc[doc,day,AM])
    + am_shortfall[day]
    >= sun_am_min
);

constraint forall(day in days where day mod 7 = 0)(
    sum(doc in docs)(alloc[doc,day,PM])
    + pm_shortfall[day]
    >= sun_pm_min
);

%%OBJECTIVE
var int: total_am_shortfall =
    sum(day in days)(am_shortfall[day]);

var int: total_pm_shortfall =
    sum(day in days)(pm_shortfall[day]);



%%_______________________________________________________
%%_______________________________________________________
%%_______________________________________________________
%%_______________________________________________________
%%__________________SOLVE _______________________________
%%_______________________________________________________
%%_______________________________________________________
%%_______________________________________________________

%solve minimize
%    1000 * total_am_shortfall
%  + 1000 * total_pm_shortfall;
  
%%-----------------------------------------------------
%%-----------------END SOLVE  -------------------------  
%%-----------------------------------------------------

%%-----------------------------------------------------
%%-----------------ALLOC SIC from alloc----------------  
%%-----------------------------------------------------



%%-----------------------------------------------------
%%-----------------END ALLOC SIC  ---------------------  
%%-----------------------------------------------------





%%-----------------------------------------------------
%%----------------- OUTPUT------------------------------  
%%-----------------------------------------------------

%OUTPUT
output["SHOWING R \n"];
output [
	show(doc) ++ "," ++
concat([
	if     fix(roster[doc,day,l]) = 1 then "L,"
	elseif fix(alloc[doc,day,AM]) = 1 then "a,"
	elseif fix(alloc[doc,day,PM]) = 1 then "p,"
	elseif fix(alloc[doc,day,C])  = 1 then "c,"
	else   "o,"
	endif
	++ if day mod 7 = 0 then "|" else "" endif
		| day in days]
	) ++ "\n"
	| doc in docs
	];
%%	output["\n TESTDOC IS \(TESTDOC) \n"];




%%%%OUTPUT SHORTFALL STUFF
output [

  "AM shortfall = "
  ++ show(total_am_shortfall)
  ++ "\n"

  ++ "PM shortfall = "
  ++ show(total_pm_shortfall)
  ++ "\n\n"

]

++

[
  "Day "
  ++ show(day)
  ++
  "  AM="
  ++ show(am_shortfall[day])
  ++
  "  PM="
  ++ show(pm_shortfall[day])
  ++
  "\n"

  | day in days

  where fix(am_shortfall[day]) > 0
     \/ fix(pm_shortfall[day]) > 0
];

function string: alloc_symbol(docs: d, int: day) =
    if fix(alloc[d,day,AM]) = 1 then "a,"
    elseif fix(alloc[d,day,PM]) = 1 then "p,"
    elseif fix(alloc[d,day,C]) = 1 then "c,"
    elseif fix(roster[d,day,l]) = 1 then "L,"
    else "o,"
    endif;


output
[
    show(d) ++ ","
    ++ concat([alloc_symbol(d,day) ++ if day mod 7 = 0 then "|" else "" endif ++ if day mod 14 = 0 then "|" else "" endif
              | day in days])
    ++ "\n"
    | d in docs
];
