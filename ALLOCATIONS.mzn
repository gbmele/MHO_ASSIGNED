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

array[docs,days,shifts] of var 0..1: R;

constraint forall(doc in docs, day in days, sh in shifts) (
  if doc in {gmele,avarma,ccobela,awallac} then
    R[doc,day,o] = 1
  else
    R[doc,day,sh] = bool2int(roster[doc,day,sh])
  endif
);



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
int: mon_am_min=3; int: mon_am_max=6;
int: mon_pm_min=3; int: mon_pm_max=6;
int: mon_c_min=0;  int: mon_c_max=10;

int: tue_am_min=3; int: tue_am_max=6;
int: tue_pm_min=3; int: tue_pm_max=6;
int: tue_c_min=0;  int: tue_c_max=10;

int: wed_am_min=3; int: wed_am_max=6;
int: wed_pm_min=3; int: wed_pm_max=6;
int: wed_c_min=0;  int: wed_c_max=10;

int: thu_am_min=3; int: thu_am_max=6;
int: thu_pm_min=3; int: thu_pm_max=6;
int: thu_c_min=0;  int: thu_c_max=10;

int: fri_am_min=3; int: fri_am_max=6;
int: fri_pm_min=3; int: fri_pm_max=6;
int: fri_c_min=0;  int: fri_c_max=10;

int: sat_am_min=3; int: sat_am_max=6;
int: sat_pm_min=3; int: sat_pm_max=6;

int: sun_am_min=3; int: sun_am_max=6;
int: sun_pm_min=3; int: sun_pm_max=6;

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
    = 1);

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
 
 
else
 
false
 
endif
);

%% set ps per week
predicate p_per_week(docs: doc, int: P) =
forall(mon in days where mon mod 7 = 1 /\ mon + 4 <= max(days)) 
   (sum(d in mon..mon+4)(alloc[doc,d,PM]) = P);


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%code for all docs
%% all docs no am after pm from an allocation point of view

predicate no_am_after_pm() =
  forall(doc in docs, day in days where day < max(days)) 
    (alloc[doc,day,PM] + alloc[doc,day+1,AM] <= 1);

constraint no_am_after_pm();





%%%%%% 
%temp code THIS COULD BE ANOTHERinclude file....

array[1..7] of shifts: greg_template = [c,p,o,c,ao,o,ao];

constraint alloc_template(gmele,greg_template) /\ four_shifts_week(gmele);

array[1..7] of shifts: avarma_template = [apo,c,apo,apo,apo,apo,apo];

constraint alloc_template(avarma,avarma_template) /\ three_shifts_week(avarma);
constraint apc(avarma,1,1,1);


array[1..7] of shifts: ccobela_template=[apo,ao,ao,ao,apo,apo,apo];

constraint forall(doc in {ccobela})
          (alloc_template(doc,ccobela_template) /\ 
          four_shifts_week(doc) /\
%          ap(doc,3,1) /\
          p_per_week(doc,1) /\
          n_fri_pm[doc] in 1..2 /\
          n_sat_am[doc]=2 /\ n_sun_am[doc]=2 /\ n_sat_pm[doc]=0 /\ n_sun_pm[doc]=0 /\
          no_split_weekends(doc));
          
          
array[1..14] of shifts: awallac_template =[apo,ao,ao,ao,apo,apo,apo, o,o,o,o,o,o,o];

constraint alloc_template14(awallac,awallac_template);
constraint shifts_per_fortnight(awallac,3);
                    
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




%OUTPUT
output["SHOWING R \n"];
output [
	show(doc) ++ "," ++
concat([
	if     fix(alloc[doc,day,AM]) = 1 then "a,"
	elseif fix(alloc[doc,day,PM]) = 1 then "p,"
	elseif fix(alloc[doc,day,C])  = 1 then "c,"
	else   "o,"
	endif
		| day in days]
	) ++ "\n"
	| doc in docs
	];