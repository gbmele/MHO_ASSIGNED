include "globals.mzn" ;           

% include "global_calendar.mzn"  ;  

int: DAYS = 14 ; 
enum shifts =   {o,a,p,c,l,s,i,erl,al,cl,lsl,mat,pat,lwop,sab,phnw,apo ,x ,oc,}; 

enum docs = {yperera,skapita,aroseng,mlynch,jlim,jchan,kvu,hlauren,xhoo,lward,lclarke,mlew,parcher,kmoussa,tbridga,mchong,rprimro,avarma,bmc,ssurka,dlowman,dbui,lsmith,gmele,rmarson,ewoodwa,cknight,lbridgf,awallac,ccobela,} ;

array[docs,1..DAYS,shifts] of var bool: roster ; 

%% this is the key -- it sets all the other shifts not declared by me  to be false
constraint forall(d in docs, day in 1..DAYS)(       
   sum(sh in shifts)(bool2int(roster[d,day,sh])) = 1 ); 

array[docs] of var int: target_s;    

array[docs] of var int: target_i;    

array[docs] of var int: target_oc;    

    

array[docs] of var int: min_s;    

array[docs] of var int: min_i;    

array[docs] of var int: min_oc;    

array[docs,1..DAYS] of var bool: ssu;    

array[docs,1..DAYS] of var bool: inc;    

array[docs,1..DAYS] of var bool: occ;    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

% ROLE MUST MATCH UNDERLYING SHIFTS    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

constraint forall(d in docs, day in 1..DAYS)(    

  ssu[d,day] -> roster[d,day,a] = 1);    

constraint forall(d in docs, day in 1..DAYS)(    

  inc[d,day] -> roster[d,day,a] = 1 );    

     

constraint forall(d in docs, day in 1..DAYS)(    

  occ[d,day] -> roster[d,day,p] = 1);    

     

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

% DAILY REQUIREMENTS    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

constraint forall(day in 1..DAYS)(    

sum(d in docs)(bool2int(ssu[d,day])) = 1    

);    

constraint forall(day in 1..DAYS)(    

sum(d in docs)(bool2int(inc[d,day])) = 1    

);    

constraint forall(day in 1..DAYS)(    

sum(d in docs)(bool2int(occ[d,day])) = 1    

);    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

% S AND I CANNOT BE THE SAME PERSON    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

     

constraint forall(d in docs, day in 1..DAYS)(    

bool2int(ssu[d,day]) +    

bool2int(inc[d,day]) <= 1    

);    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

% COUNT ASSIGNMENTS PER DOCTOR    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

array[docs] of var int: n_s;    

array[docs] of var int: n_i;    

array[docs] of var int: n_oc;    

     

constraint forall(d in docs)(    

n_s[d] =    

sum(day in 1..DAYS)(bool2int(ssu[d,day]))    

);    

     

constraint forall(d in docs)(    

n_i[d] =    

sum(day in 1..DAYS)(bool2int(inc[d,day]))    

);    

     

constraint forall(d in docs)(    

n_oc[d] =    

sum(day in 1..DAYS)(bool2int(occ[d,day]))    

);    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

% TARGETS    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

constraint forall(d in docs)(    

n_s[d] <= target_s[d]);    

constraint forall(d in docs)(    

n_i[d] <= target_i[d]    

);    

constraint forall(d in docs)(    

n_oc[d] <= target_oc[d]  /\ n_oc[d] >=min_oc[d]  

);    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

% NO MORE THAN ONE OC IN ANY min_oc_gap DAY WINDOW    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

     

int: min_oc_gap=14;    

constraint    

forall(d in docs, day in 1..DAYS-min_oc_gap+1)(    

sum(k in day..day+min_oc_gap-1)(    

bool2int(occ[d,k])    

) <= 1    

);    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

% NO MORE THAN ONE INC IN ANY min_inc_gap DAY WINDOW    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

     

int: min_inc_gap=2;    

constraint    

forall(d in docs, day in 1..DAYS-min_inc_gap+1)(    

sum(k in day..day+min_inc_gap-1)(    

bool2int(inc[d,k])    

) <= 1    

);    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

% NO MORE THAN ONE SSU IN ANY min_ssu_gap DAY WINDOW    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

     

int: min_ssu_gap=2;    

constraint    

forall(d in docs, day in 1..DAYS-min_ssu_gap+1)(    

sum(k in day..day+min_ssu_gap-1)(    

bool2int(ssu[d,k])    

) <= 1    

);    

output["\nSSU\n"];  

output [  

show([d | d in docs where fix(ssu[d,day]) = true]) ++"," | day in 1..DAYS ]; 

output["\n\n"];  

output [  

show([d | d in docs where fix(inc[d,day]) = true]) ++"," | day in 1..DAYS ]; 

output["\n\n"];  

output [  

show([d | d in docs where fix(occ[d,day]) = true]) ++"," | day in 1..DAYS ]; 

output["\n\n"];  

% print roster
output [ 
  show(d) ++ "," ++    

  concat([     

  show(sh) ++ ","    

  | day in 1..DAYS,    

  sh in shifts    

  where fix(roster[d,day,sh])])++ "\n"| d in docs]; 

%% SIC COUNTS
output [     
  show(d)     
  ++ " \t\tS = " ++ show(n_s[d])     
  ++ " \tI = " ++ show(n_i[d])     
  ++ " \tOC = " ++ show(n_oc[d])     
  ++ "\n"     
  | d in docs       
  ];     
predicate set_SIC(docs:doc,int:S,int:I,int:OC_min,int:OC_max)= 
  (target_s[doc]= S /\ target_i[doc] = I /\ min_oc[doc]=OC_min /\ target_oc[doc]=OC_max); 


constraint set_SIC(yperera,5,5,0,5); 
constraint set_SIC(skapita,5,5,0,5); 
constraint set_SIC(aroseng,5,5,0,5); 
constraint set_SIC(mlynch,5,5,0,5); 
constraint set_SIC(jlim,5,5,0,5); 
constraint set_SIC(jchan,5,5,0,5); 
constraint set_SIC(kvu,5,5,0,5); 
constraint set_SIC(hlauren,5,5,0,5); 
constraint set_SIC(xhoo,5,5,0,5); 
constraint set_SIC(lward,5,5,0,5); 
constraint set_SIC(lclarke,5,5,0,5); 
constraint set_SIC(mlew,5,5,0,5); 
constraint set_SIC(parcher,5,5,0,5); 
constraint set_SIC(kmoussa,5,5,0,5); 
constraint set_SIC(tbridga,5,5,0,5); 
constraint set_SIC(mchong,5,5,0,5); 
constraint set_SIC(rprimro,5,5,0,5); 
constraint set_SIC(avarma,5,5,0,5); 
constraint set_SIC(bmc,5,5,0,5); 
constraint set_SIC(ssurka,5,5,0,5); 
constraint set_SIC(dlowman,5,5,0,5); 
constraint set_SIC(dbui,5,5,0,5); 
constraint set_SIC(lsmith,5,5,0,5); 
constraint set_SIC(gmele,5,5,0,0); 
constraint set_SIC(rmarson,5,5,0,5); 
constraint set_SIC(ewoodwa,5,5,0,5); 
constraint set_SIC(cknight,5,5,0,5); 
constraint set_SIC(lbridgf,5,5,0,5); 
constraint set_SIC(awallac,5,5,0,5); 
constraint set_SIC(ccobela,5,5,0,5); 

constraint roster[yperera,1,o] = 1 ; 
constraint roster[yperera,2,o] = 1 ; 
constraint roster[yperera,3,o] = 1 ; 
constraint roster[yperera,4,o] = 1 ; 
constraint roster[yperera,5,o] = 1 ; 
constraint roster[yperera,6,o] = 1 ; 
constraint roster[yperera,7,o] = 1 ; 
constraint roster[yperera,8,o] = 1 ; 
constraint roster[yperera,9,o] = 1 ; 
constraint roster[yperera,10,o] = 1 ; 
constraint roster[yperera,11,p] = 1 ; 
constraint roster[yperera,12,o] = 1 ; 
constraint roster[yperera,13,o] = 1 ; 
constraint roster[yperera,14,o] = 1 ; 
constraint roster[skapita,1,a] = 1 ; 
constraint roster[skapita,2,a] = 1 ; 
constraint roster[skapita,3,p] = 1 ; 
constraint roster[skapita,4,o] = 1 ; 
constraint roster[skapita,5,o] = 1 ; 
constraint roster[skapita,6,o] = 1 ; 
constraint roster[skapita,7,o] = 1 ; 
constraint roster[skapita,8,a] = 1 ; 
constraint roster[skapita,9,a] = 1 ; 
constraint roster[skapita,10,p] = 1 ; 
constraint roster[skapita,11,o] = 1 ; 
constraint roster[skapita,12,o] = 1 ; 
constraint roster[skapita,13,o] = 1 ; 
constraint roster[skapita,14,o] = 1 ; 
constraint roster[aroseng,1,o] = 1 ; 
constraint roster[aroseng,2,o] = 1 ; 
constraint roster[aroseng,3,o] = 1 ; 
constraint roster[aroseng,4,o] = 1 ; 
constraint roster[aroseng,5,o] = 1 ; 
constraint roster[aroseng,6,o] = 1 ; 
constraint roster[aroseng,7,o] = 1 ; 
constraint roster[aroseng,8,o] = 1 ; 
constraint roster[aroseng,9,o] = 1 ; 
constraint roster[aroseng,10,a] = 1 ; 
constraint roster[aroseng,11,a] = 1 ; 
constraint roster[aroseng,12,o] = 1 ; 
constraint roster[aroseng,13,o] = 1 ; 
constraint roster[aroseng,14,o] = 1 ; 
constraint roster[mlynch,1,o] = 1 ; 
constraint roster[mlynch,2,o] = 1 ; 
constraint roster[mlynch,3,p] = 1 ; 
constraint roster[mlynch,4,o] = 1 ; 
constraint roster[mlynch,5,o] = 1 ; 
constraint roster[mlynch,6,o] = 1 ; 
constraint roster[mlynch,7,o] = 1 ; 
constraint roster[mlynch,8,o] = 1 ; 
constraint roster[mlynch,9,o] = 1 ; 
constraint roster[mlynch,10,o] = 1 ; 
constraint roster[mlynch,11,o] = 1 ; 
constraint roster[mlynch,12,o] = 1 ; 
constraint roster[mlynch,13,o] = 1 ; 
constraint roster[mlynch,14,o] = 1 ; 
constraint roster[jlim,1,o] = 1 ; 
constraint roster[jlim,2,o] = 1 ; 
constraint roster[jlim,3,c] = 1 ; 
constraint roster[jlim,4,o] = 1 ; 
constraint roster[jlim,5,o] = 1 ; 
constraint roster[jlim,6,a] = 1 ; 
constraint roster[jlim,7,a] = 1 ; 
constraint roster[jlim,8,o] = 1 ; 
constraint roster[jlim,9,p] = 1 ; 
constraint roster[jlim,10,c] = 1 ; 
constraint roster[jlim,11,p] = 1 ; 
constraint roster[jlim,12,o] = 1 ; 
constraint roster[jlim,13,o] = 1 ; 
constraint roster[jlim,14,o] = 1 ; 
constraint roster[jchan,1,p] = 1 ; 
constraint roster[jchan,2,o] = 1 ; 
constraint roster[jchan,3,o] = 1 ; 
constraint roster[jchan,4,o] = 1 ; 
constraint roster[jchan,5,o] = 1 ; 
constraint roster[jchan,6,a] = 1 ; 
constraint roster[jchan,7,o] = 1 ; 
constraint roster[jchan,8,o] = 1 ; 
constraint roster[jchan,9,o] = 1 ; 
constraint roster[jchan,10,o] = 1 ; 
constraint roster[jchan,11,o] = 1 ; 
constraint roster[jchan,12,o] = 1 ; 
constraint roster[jchan,13,o] = 1 ; 
constraint roster[jchan,14,o] = 1 ; 
constraint roster[kvu,1,o] = 1 ; 
constraint roster[kvu,2,a] = 1 ; 
constraint roster[kvu,3,a] = 1 ; 
constraint roster[kvu,4,o] = 1 ; 
constraint roster[kvu,5,o] = 1 ; 
constraint roster[kvu,6,p] = 1 ; 
constraint roster[kvu,7,p] = 1 ; 
constraint roster[kvu,8,o] = 1 ; 
constraint roster[kvu,9,o] = 1 ; 
constraint roster[kvu,10,o] = 1 ; 
constraint roster[kvu,11,o] = 1 ; 
constraint roster[kvu,12,o] = 1 ; 
constraint roster[kvu,13,o] = 1 ; 
constraint roster[kvu,14,o] = 1 ; 
constraint roster[hlauren,1,o] = 1 ; 
constraint roster[hlauren,2,c] = 1 ; 
constraint roster[hlauren,3,a] = 1 ; 
constraint roster[hlauren,4,a] = 1 ; 
constraint roster[hlauren,5,p] = 1 ; 
constraint roster[hlauren,6,o] = 1 ; 
constraint roster[hlauren,7,o] = 1 ; 
constraint roster[hlauren,8,a] = 1 ; 
constraint roster[hlauren,9,a] = 1 ; 
constraint roster[hlauren,10,c] = 1 ; 
constraint roster[hlauren,11,p] = 1 ; 
constraint roster[hlauren,12,o] = 1 ; 
constraint roster[hlauren,13,o] = 1 ; 
constraint roster[hlauren,14,o] = 1 ; 
constraint roster[xhoo,1,a] = 1 ; 
constraint roster[xhoo,2,o] = 1 ; 
constraint roster[xhoo,3,o] = 1 ; 
constraint roster[xhoo,4,o] = 1 ; 
constraint roster[xhoo,5,p] = 1 ; 
constraint roster[xhoo,6,o] = 1 ; 
constraint roster[xhoo,7,o] = 1 ; 
constraint roster[xhoo,8,o] = 1 ; 
constraint roster[xhoo,9,o] = 1 ; 
constraint roster[xhoo,10,o] = 1 ; 
constraint roster[xhoo,11,o] = 1 ; 
constraint roster[xhoo,12,o] = 1 ; 
constraint roster[xhoo,13,o] = 1 ; 
constraint roster[xhoo,14,o] = 1 ; 
constraint roster[lward,1,o] = 1 ; 
constraint roster[lward,2,o] = 1 ; 
constraint roster[lward,3,o] = 1 ; 
constraint roster[lward,4,o] = 1 ; 
constraint roster[lward,5,o] = 1 ; 
constraint roster[lward,6,p] = 1 ; 
constraint roster[lward,7,p] = 1 ; 
constraint roster[lward,8,o] = 1 ; 
constraint roster[lward,9,o] = 1 ; 
constraint roster[lward,10,o] = 1 ; 
constraint roster[lward,11,o] = 1 ; 
constraint roster[lward,12,o] = 1 ; 
constraint roster[lward,13,o] = 1 ; 
constraint roster[lward,14,o] = 1 ; 
constraint roster[lclarke,1,o] = 1 ; 
constraint roster[lclarke,2,p] = 1 ; 
constraint roster[lclarke,3,o] = 1 ; 
constraint roster[lclarke,4,a] = 1 ; 
constraint roster[lclarke,5,p] = 1 ; 
constraint roster[lclarke,6,p] = 1 ; 
constraint roster[lclarke,7,p] = 1 ; 
constraint roster[lclarke,8,o] = 1 ; 
constraint roster[lclarke,9,p] = 1 ; 
constraint roster[lclarke,10,o] = 1 ; 
constraint roster[lclarke,11,a] = 1 ; 
constraint roster[lclarke,12,o] = 1 ; 
constraint roster[lclarke,13,o] = 1 ; 
constraint roster[lclarke,14,o] = 1 ; 
constraint roster[mlew,1,o] = 1 ; 
constraint roster[mlew,2,o] = 1 ; 
constraint roster[mlew,3,a] = 1 ; 
constraint roster[mlew,4,a] = 1 ; 
constraint roster[mlew,5,o] = 1 ; 
constraint roster[mlew,6,o] = 1 ; 
constraint roster[mlew,7,a] = 1 ; 
constraint roster[mlew,8,o] = 1 ; 
constraint roster[mlew,9,o] = 1 ; 
constraint roster[mlew,10,a] = 1 ; 
constraint roster[mlew,11,a] = 1 ; 
constraint roster[mlew,12,o] = 1 ; 
constraint roster[mlew,13,o] = 1 ; 
constraint roster[mlew,14,p] = 1 ; 
constraint roster[parcher,1,o] = 1 ; 
constraint roster[parcher,2,a] = 1 ; 
constraint roster[parcher,3,o] = 1 ; 
constraint roster[parcher,4,o] = 1 ; 
constraint roster[parcher,5,o] = 1 ; 
constraint roster[parcher,6,o] = 1 ; 
constraint roster[parcher,7,o] = 1 ; 
constraint roster[parcher,8,o] = 1 ; 
constraint roster[parcher,9,a] = 1 ; 
constraint roster[parcher,10,o] = 1 ; 
constraint roster[parcher,11,o] = 1 ; 
constraint roster[parcher,12,o] = 1 ; 
constraint roster[parcher,13,o] = 1 ; 
constraint roster[parcher,14,o] = 1 ; 
constraint roster[kmoussa,1,p] = 1 ; 
constraint roster[kmoussa,2,o] = 1 ; 
constraint roster[kmoussa,3,o] = 1 ; 
constraint roster[kmoussa,4,o] = 1 ; 
constraint roster[kmoussa,5,o] = 1 ; 
constraint roster[kmoussa,6,o] = 1 ; 
constraint roster[kmoussa,7,o] = 1 ; 
constraint roster[kmoussa,8,p] = 1 ; 
constraint roster[kmoussa,9,o] = 1 ; 
constraint roster[kmoussa,10,o] = 1 ; 
constraint roster[kmoussa,11,o] = 1 ; 
constraint roster[kmoussa,12,o] = 1 ; 
constraint roster[kmoussa,13,o] = 1 ; 
constraint roster[kmoussa,14,o] = 1 ; 
constraint roster[tbridga,1,o] = 1 ; 
constraint roster[tbridga,2,o] = 1 ; 
constraint roster[tbridga,3,c] = 1 ; 
constraint roster[tbridga,4,o] = 1 ; 
constraint roster[tbridga,5,o] = 1 ; 
constraint roster[tbridga,6,o] = 1 ; 
constraint roster[tbridga,7,o] = 1 ; 
constraint roster[tbridga,8,o] = 1 ; 
constraint roster[tbridga,9,a] = 1 ; 
constraint roster[tbridga,10,c] = 1 ; 
constraint roster[tbridga,11,o] = 1 ; 
constraint roster[tbridga,12,p] = 1 ; 
constraint roster[tbridga,13,o] = 1 ; 
constraint roster[tbridga,14,o] = 1 ; 
constraint roster[mchong,1,o] = 1 ; 
constraint roster[mchong,2,a] = 1 ; 
constraint roster[mchong,3,p] = 1 ; 
constraint roster[mchong,4,c] = 1 ; 
constraint roster[mchong,5,o] = 1 ; 
constraint roster[mchong,6,o] = 1 ; 
constraint roster[mchong,7,a] = 1 ; 
constraint roster[mchong,8,o] = 1 ; 
constraint roster[mchong,9,o] = 1 ; 
constraint roster[mchong,10,p] = 1 ; 
constraint roster[mchong,11,c] = 1 ; 
constraint roster[mchong,12,a] = 1 ; 
constraint roster[mchong,13,p] = 1 ; 
constraint roster[mchong,14,o] = 1 ; 
constraint roster[rprimro,1,o] = 1 ; 
constraint roster[rprimro,2,o] = 1 ; 
constraint roster[rprimro,3,o] = 1 ; 
constraint roster[rprimro,4,c] = 1 ; 
constraint roster[rprimro,5,o] = 1 ; 
constraint roster[rprimro,6,o] = 1 ; 
constraint roster[rprimro,7,p] = 1 ; 
constraint roster[rprimro,8,o] = 1 ; 
constraint roster[rprimro,9,c] = 1 ; 
constraint roster[rprimro,10,a] = 1 ; 
constraint roster[rprimro,11,c] = 1 ; 
constraint roster[rprimro,12,o] = 1 ; 
constraint roster[rprimro,13,o] = 1 ; 
constraint roster[rprimro,14,p] = 1 ; 
constraint roster[avarma,1,o] = 1 ; 
constraint roster[avarma,2,c] = 1 ; 
constraint roster[avarma,3,p] = 1 ; 
constraint roster[avarma,4,o] = 1 ; 
constraint roster[avarma,5,a] = 1 ; 
constraint roster[avarma,6,o] = 1 ; 
constraint roster[avarma,7,o] = 1 ; 
constraint roster[avarma,8,o] = 1 ; 
constraint roster[avarma,9,c] = 1 ; 
constraint roster[avarma,10,p] = 1 ; 
constraint roster[avarma,11,o] = 1 ; 
constraint roster[avarma,12,o] = 1 ; 
constraint roster[avarma,13,a] = 1 ; 
constraint roster[avarma,14,a] = 1 ; 
constraint roster[bmc,1,o] = 1 ; 
constraint roster[bmc,2,o] = 1 ; 
constraint roster[bmc,3,o] = 1 ; 
constraint roster[bmc,4,p] = 1 ; 
constraint roster[bmc,5,o] = 1 ; 
constraint roster[bmc,6,p] = 1 ; 
constraint roster[bmc,7,o] = 1 ; 
constraint roster[bmc,8,o] = 1 ; 
constraint roster[bmc,9,o] = 1 ; 
constraint roster[bmc,10,o] = 1 ; 
constraint roster[bmc,11,p] = 1 ; 
constraint roster[bmc,12,o] = 1 ; 
constraint roster[bmc,13,o] = 1 ; 
constraint roster[bmc,14,o] = 1 ; 
constraint roster[ssurka,1,a] = 1 ; 
constraint roster[ssurka,2,a] = 1 ; 
constraint roster[ssurka,3,o] = 1 ; 
constraint roster[ssurka,4,o] = 1 ; 
constraint roster[ssurka,5,o] = 1 ; 
constraint roster[ssurka,6,o] = 1 ; 
constraint roster[ssurka,7,o] = 1 ; 
constraint roster[ssurka,8,p] = 1 ; 
constraint roster[ssurka,9,p] = 1 ; 
constraint roster[ssurka,10,o] = 1 ; 
constraint roster[ssurka,11,o] = 1 ; 
constraint roster[ssurka,12,o] = 1 ; 
constraint roster[ssurka,13,o] = 1 ; 
constraint roster[ssurka,14,o] = 1 ; 
constraint roster[dlowman,1,o] = 1 ; 
constraint roster[dlowman,2,p] = 1 ; 
constraint roster[dlowman,3,c] = 1 ; 
constraint roster[dlowman,4,a] = 1 ; 
constraint roster[dlowman,5,a] = 1 ; 
constraint roster[dlowman,6,o] = 1 ; 
constraint roster[dlowman,7,o] = 1 ; 
constraint roster[dlowman,8,a] = 1 ; 
constraint roster[dlowman,9,a] = 1 ; 
constraint roster[dlowman,10,c] = 1 ; 
constraint roster[dlowman,11,o] = 1 ; 
constraint roster[dlowman,12,p] = 1 ; 
constraint roster[dlowman,13,o] = 1 ; 
constraint roster[dlowman,14,o] = 1 ; 
constraint roster[dbui,1,a] = 1 ; 
constraint roster[dbui,2,p] = 1 ; 
constraint roster[dbui,3,o] = 1 ; 
constraint roster[dbui,4,c] = 1 ; 
constraint roster[dbui,5,a] = 1 ; 
constraint roster[dbui,6,o] = 1 ; 
constraint roster[dbui,7,o] = 1 ; 
constraint roster[dbui,8,o] = 1 ; 
constraint roster[dbui,9,p] = 1 ; 
constraint roster[dbui,10,o] = 1 ; 
constraint roster[dbui,11,o] = 1 ; 
constraint roster[dbui,12,a] = 1 ; 
constraint roster[dbui,13,a] = 1 ; 
constraint roster[dbui,14,a] = 1 ; 
constraint roster[lsmith,1,p] = 1 ; 
constraint roster[lsmith,2,o] = 1 ; 
constraint roster[lsmith,3,c] = 1 ; 
constraint roster[lsmith,4,o] = 1 ; 
constraint roster[lsmith,5,a] = 1 ; 
constraint roster[lsmith,6,o] = 1 ; 
constraint roster[lsmith,7,o] = 1 ; 
constraint roster[lsmith,8,p] = 1 ; 
constraint roster[lsmith,9,o] = 1 ; 
constraint roster[lsmith,10,c] = 1 ; 
constraint roster[lsmith,11,o] = 1 ; 
constraint roster[lsmith,12,o] = 1 ; 
constraint roster[lsmith,13,a] = 1 ; 
constraint roster[lsmith,14,o] = 1 ; 
constraint roster[gmele,1,c] = 1 ; 
constraint roster[gmele,2,p] = 1 ; 
constraint roster[gmele,3,o] = 1 ; 
constraint roster[gmele,4,c] = 1 ; 
constraint roster[gmele,5,o] = 1 ; 
constraint roster[gmele,6,a] = 1 ; 
constraint roster[gmele,7,o] = 1 ; 
constraint roster[gmele,8,c] = 1 ; 
constraint roster[gmele,9,p] = 1 ; 
constraint roster[gmele,10,o] = 1 ; 
constraint roster[gmele,11,c] = 1 ; 
constraint roster[gmele,12,o] = 1 ; 
constraint roster[gmele,13,o] = 1 ; 
constraint roster[gmele,14,a] = 1 ; 
constraint roster[rmarson,1,a] = 1 ; 
constraint roster[rmarson,2,p] = 1 ; 
constraint roster[rmarson,3,c] = 1 ; 
constraint roster[rmarson,4,o] = 1 ; 
constraint roster[rmarson,5,a] = 1 ; 
constraint roster[rmarson,6,o] = 1 ; 
constraint roster[rmarson,7,o] = 1 ; 
constraint roster[rmarson,8,a] = 1 ; 
constraint roster[rmarson,9,o] = 1 ; 
constraint roster[rmarson,10,c] = 1 ; 
constraint roster[rmarson,11,a] = 1 ; 
constraint roster[rmarson,12,p] = 1 ; 
constraint roster[rmarson,13,o] = 1 ; 
constraint roster[rmarson,14,o] = 1 ; 
constraint roster[ewoodwa,1,o] = 1 ; 
constraint roster[ewoodwa,2,o] = 1 ; 
constraint roster[ewoodwa,3,o] = 1 ; 
constraint roster[ewoodwa,4,p] = 1 ; 
constraint roster[ewoodwa,5,o] = 1 ; 
constraint roster[ewoodwa,6,o] = 1 ; 
constraint roster[ewoodwa,7,o] = 1 ; 
constraint roster[ewoodwa,8,o] = 1 ; 
constraint roster[ewoodwa,9,o] = 1 ; 
constraint roster[ewoodwa,10,o] = 1 ; 
constraint roster[ewoodwa,11,o] = 1 ; 
constraint roster[ewoodwa,12,o] = 1 ; 
constraint roster[ewoodwa,13,p] = 1 ; 
constraint roster[ewoodwa,14,o] = 1 ; 
constraint roster[cknight,1,p] = 1 ; 
constraint roster[cknight,2,o] = 1 ; 
constraint roster[cknight,3,o] = 1 ; 
constraint roster[cknight,4,p] = 1 ; 
constraint roster[cknight,5,p] = 1 ; 
constraint roster[cknight,6,o] = 1 ; 
constraint roster[cknight,7,o] = 1 ; 
constraint roster[cknight,8,o] = 1 ; 
constraint roster[cknight,9,o] = 1 ; 
constraint roster[cknight,10,o] = 1 ; 
constraint roster[cknight,11,o] = 1 ; 
constraint roster[cknight,12,o] = 1 ; 
constraint roster[cknight,13,p] = 1 ; 
constraint roster[cknight,14,p] = 1 ; 
constraint roster[lbridgf,1,a] = 1 ; 
constraint roster[lbridgf,2,o] = 1 ; 
constraint roster[lbridgf,3,a] = 1 ; 
constraint roster[lbridgf,4,o] = 1 ; 
constraint roster[lbridgf,5,o] = 1 ; 
constraint roster[lbridgf,6,a] = 1 ; 
constraint roster[lbridgf,7,a] = 1 ; 
constraint roster[lbridgf,8,o] = 1 ; 
constraint roster[lbridgf,9,a] = 1 ; 
constraint roster[lbridgf,10,a] = 1 ; 
constraint roster[lbridgf,11,o] = 1 ; 
constraint roster[lbridgf,12,o] = 1 ; 
constraint roster[lbridgf,13,o] = 1 ; 
constraint roster[lbridgf,14,o] = 1 ; 
constraint roster[awallac,1,o] = 1 ; 
constraint roster[awallac,2,o] = 1 ; 
constraint roster[awallac,3,o] = 1 ; 
constraint roster[awallac,4,o] = 1 ; 
constraint roster[awallac,5,o] = 1 ; 
constraint roster[awallac,6,o] = 1 ; 
constraint roster[awallac,7,o] = 1 ; 
constraint roster[awallac,8,o] = 1 ; 
constraint roster[awallac,9,o] = 1 ; 
constraint roster[awallac,10,o] = 1 ; 
constraint roster[awallac,11,o] = 1 ; 
constraint roster[awallac,12,a] = 1 ; 
constraint roster[awallac,13,o] = 1 ; 
constraint roster[awallac,14,o] = 1 ; 
constraint roster[ccobela,1,o] = 1 ; 
constraint roster[ccobela,2,a] = 1 ; 
constraint roster[ccobela,3,a] = 1 ; 
constraint roster[ccobela,4,a] = 1 ; 
constraint roster[ccobela,5,p] = 1 ; 
constraint roster[ccobela,6,o] = 1 ; 
constraint roster[ccobela,7,o] = 1 ; 
constraint roster[ccobela,8,p] = 1 ; 
constraint roster[ccobela,9,o] = 1 ; 
constraint roster[ccobela,10,a] = 1 ; 
constraint roster[ccobela,11,a] = 1 ; 
constraint roster[ccobela,12,a] = 1 ; 
constraint roster[ccobela,13,o] = 1 ; 
constraint roster[ccobela,14,o] = 1 ; 
