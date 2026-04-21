theory LRE_Z_Machine_deadlock_free

imports "Z_Machines.Z_Machine"
begin

notation undefined ("???")

subsection \<open> Introduction \<close>

text \<open> This theory file is to model the LRE_Beh state machine in Z Machine notations.\<close>

subsection \<open> type definition \<close>

enumtype St = OCM | MOM | HCM | CAM | initial 

enumtype Evt = advVel | reqHCM | reqOCM | reqMOM | endTask | reqVel 


datatype ('s, 'e) tag =
  State (ofState: 's) | Event (ofEvent: 'e)

abbreviation "is_Event x \<equiv> \<not> is_State x"

type_synonym ('s, 'e) rctrace = "('s, 'e) tag list"

definition wf_rcstore :: "('s, 'e) rctrace \<Rightarrow> 's \<Rightarrow> 's option \<Rightarrow> bool" where
[z_defs]: "wf_rcstore tr st final = 
    (length(tr) > 0 
   \<and> tr ! ((length tr) -1) = State st 
   \<and> ( final \<noteq> None \<longrightarrow> (\<forall>i<length tr. tr ! i = State (the final) \<longrightarrow> i= (length tr) -1)) 
   \<and> (filter is_State tr) ! (length (filter is_State tr) -1) = State  st)"

type_synonym coord="integer\<times>integer"

record Obstacle =
  obspos :: coord
  id :: nat

consts Obsts :: " coord list"

consts Positions::"coord set"

consts Velocities:: "(integer\<times>integer) set"

consts HCMVel:: "integer"

consts MOMVel:: "integer"

consts MinSafeDist :: "integer"


consts Opez_min:: "coord"
consts Opez_max:: "coord"
consts SafeVel :: "integer"
consts ZeroVel:: "coord"

text \<open> function definition \<close>


fun inOPEZ:: "coord\<Rightarrow> bool"
  where "inOPEZ (x,y) = ( x\<ge> fst Opez_min \<and> x< fst Opez_max \<and> y\<ge>snd Opez_min \<and> y<fst Opez_max)"



fun single_dist:: " coord \<times> coord  \<Rightarrow> integer"
  where "single_dist((x,y), (m,n)) =(x-m)^2+ (y-n)^2"


fun dist:: " coord \<times> (coord list) \<Rightarrow> integer"
  where 
"dist((x,y),[]) = 200^2+ 200^2" |
 " dist((x,y), g#gs) =( if  single_dist((x,y),g) \<le> dist ((x,y),gs) then single_dist((x,y),g) else dist ((x,y),gs))"

fun obst_index:: "coord  \<times> (coord list) \<Rightarrow> nat"
  where
"obst_index ((x,y), [])=100 " |
 "obst_index ((x,y), g#gs)= (if single_dist ((x,y),g) = dist ((x,y),g#gs) then 0 else  (obst_index ((x,y), gs)+1))"



fun abslt:: "integer\<Rightarrow> integer"
  where "abslt(x) = (if x\<ge>0 then x else -x)"


fun closestObs_xpos :: "coord \<times> (coord list) \<Rightarrow> integer"
  where "closestObs_xpos((xp,yp),[]) = 1000000"|
        "closestObs_xpos((xp,yp),g#gs) = fst ((g#gs) ! obst_index((xp,yp), g#gs))"

fun closestObs_ypos :: "coord \<times> (coord list) \<Rightarrow> integer"
  where "closestObs_ypos((xp,yp),[]) = 1000000"|
        "closestObs_ypos((xp,yp),g#gs) = snd ((g#gs) ! obst_index((xp,yp), g#gs))"


fun CDA :: " coord \<times> (coord list)\<times> (integer \<times> integer) \<Rightarrow> integer"
  where "CDA((xp,yp),[], (xv,yv)) = (10+MinSafeDist+5)^2" |
"CDA ((xp,yp), g#gs, (xv,yv)) = 
(if xv\<noteq>0 \<and> yv=0 
 then
  (if (closestObs_xpos((xp,yp),g#gs)- xp) * xv\<ge>0 
   then dist((xp,yp),g#gs) -(closestObs_xpos((xp,yp),g#gs) - xp)^2  
   else dist((xp,yp),g#gs)  ) 
else 
  (if xv=0 \<and> yv\<noteq>0
   then
    (if (closestObs_ypos((xp,yp),g#gs) - yp) * yv\<ge>0
     then dist((xp,yp),g#gs)- (closestObs_ypos((xp,yp),g#gs) - yp)^2 
     else dist((xp,yp),g#gs)  )
   else dist((xp,yp),g#gs)  ) 
)"


fun maneuv :: "integer\<times> integer \<Rightarrow> integer\<times> integer"
  where "maneuv(x,y) = (y,-x)"


fun setVel :: "(integer \<times> integer) \<times> integer   \<Rightarrow>   (integer \<times> integer) " 
  where
 "setVel((xv, yv), setpoint) =
(if xv=0 
  then 
   (if yv>0 
    then (0, setpoint) 
    else  ( if yv<0 then(0, (- setpoint) )
             else (setpoint, 0) ) )
else 
   (if xv>0 
    then (setpoint, 0) 
    else ((-setpoint), 0) )  )"



subsection \<open> State Space \<close>

(*pos::"Coord"*)
zstore LRE_Beh =
  pos:: "coord"
  xvel :: "integer"
  yvel :: "integer"
  advV::" integer\<times> integer"
  st::"St"
  tr :: "(St, Evt)tag list"
  triggers:: "Evt set"
  where inv: 
           "wf_rcstore tr st None" 



subsection \<open> Operations \<close>

zoperation Move = 
over LRE_Beh
update "[
        pos\<Zprime>=(fst(pos) + xvel, snd(pos) + yvel)
        ]"



zoperation Display = 
over LRE_Beh
params  p \<in> "{pos}" v \<in> "{(xvel,yvel)}" t\<in>"{tr}" state\<in> "{st}" 

zoperation InitialToOCM =
  over LRE_Beh
  pre "st= initial"
  update "[ st\<Zprime>= OCM
  		  , tr\<Zprime>=tr @ [State OCM]
         , triggers\<Zprime> = {reqMOM, reqVel}
          ]"

zoperation OCMToMOM =
  over LRE_Beh
  pre "st= OCM  \<and> ( xvel^2 +  yvel^2)\<le>  SafeVel^2 \<and> dist(pos,Obsts)>  (MinSafeDist+10)^2 \<and> \<not>inOPEZ(pos)"
  update "[ st\<Zprime>= MOM
  		  , tr\<Zprime>=tr  @ [Event reqMOM]  @ [Event advVel]@ [State MOM] 
        , advV\<Zprime> = setVel((xvel, yvel), MOMVel)
        , (xvel,yvel)\<Zprime> = setVel((xvel, yvel), MOMVel)
        , triggers\<Zprime> = {endTask, reqOCM}                
          ]"


zoperation MOMToOCM =
  over LRE_Beh
  pre "st= MOM"
  update "[ st\<Zprime>= OCM
  		  , tr\<Zprime>=tr @ [Event reqOCM] @ [State OCM] 
        , triggers\<Zprime> = {reqMOM, reqVel}        
          ]"

zoperation MOMToOCM_1 =
  over LRE_Beh
  pre "st= MOM \<and> inOPEZ(pos) \<and> (dist(pos,Obsts)>  (MinSafeDist+5)^2  \<or> CDA(pos,Obsts, (xvel,yvel))>  MinSafeDist^2)"
  update "[ st\<Zprime>= OCM
  		  , tr\<Zprime>=tr @ [State OCM]
        , triggers\<Zprime> = {reqMOM, reqVel}      
          ]"

        
zoperation MOMToOCM_2 =
  over LRE_Beh
  pre "st= MOM  "
  update "[ st\<Zprime>= OCM
  		  , tr\<Zprime>=tr @ [Event endTask] @ [Event advVel] @ [State OCM] 
      
        , advV\<Zprime> = ZeroVel
        , (xvel,yvel)\<Zprime> = ZeroVel
        , triggers\<Zprime> = {reqMOM, reqVel}      
          ]"

zoperation HCMToOCM =
  over LRE_Beh
  pre "st= HCM "
  update "[ st\<Zprime>= OCM
  		  , tr\<Zprime>=tr @ [Event reqOCM] @ [State OCM] 
        , triggers\<Zprime> = {reqMOM, reqVel}        
          ]"

        
zoperation HCMToOCM_1 =
  over LRE_Beh
  pre "st= HCM \<and> inOPEZ(pos)\<and> (dist(pos,Obsts)>  (MinSafeDist+5)^2  \<or> CDA(pos,Obsts, (xvel,yvel))>  MinSafeDist^2)"
  update "[ st\<Zprime>= OCM
  		  , tr\<Zprime>=tr @ [State OCM] 
        , triggers\<Zprime> = {reqMOM, reqVel}     
          ]"

zoperation MOMToHCM =
  over LRE_Beh
  pre "st= MOM \<and>  ( xvel^2 +  yvel^2)>  SafeVel^2 \<and>  dist(pos,Obsts)\<le>  (MinSafeDist+5)^2  \<and> CDA(pos,Obsts, (xvel,yvel))>  MinSafeDist^2"
  update "[ st\<Zprime>= HCM
  		  , tr\<Zprime>=tr @ [Event advVel] @ [State HCM]
        , advV\<Zprime> = setVel((xvel, yvel), HCMVel)
        , (xvel,yvel)\<Zprime> = setVel((xvel, yvel), HCMVel)
        , triggers\<Zprime> = {reqOCM}      
          ]"



zoperation HCMToMOM =
  over LRE_Beh
  pre "st= HCM \<and> dist(pos,Obsts)>  (MinSafeDist+5)^2   \<and> \<not>inOPEZ(pos) "
  update "[ st\<Zprime>= MOM
  		  , tr\<Zprime>=tr @ [Event advVel] @ [State MOM]
        , advV\<Zprime> = setVel((xvel, yvel), MOMVel)
        , (xvel,yvel)\<Zprime> =  setVel((xvel, yvel), MOMVel)
        , triggers\<Zprime> = { endTask, reqOCM}      
          ]"
        
        
zoperation OCMToOCM =
  over LRE_Beh
  params reqV \<in> " Velocities"
  pre "st= OCM  "
  update "[ st\<Zprime>= OCM
  		  , tr\<Zprime>=tr @ [Event reqVel] @ [Event advVel] @[State OCM] 
        , advV\<Zprime> = reqV
        , (xvel,yvel)\<Zprime> = reqV
        , triggers\<Zprime> = {reqMOM, reqVel}      
  ]"


         
zoperation HCMToCAM =
  over LRE_Beh
  pre "st= HCM \<and> CDA(pos,Obsts, (xvel,yvel))\<le>  MinSafeDist^2 \<and>dist(pos,Obsts) \<le>  (MinSafeDist+5)^2 "
  update "[ st\<Zprime>= CAM
  		  , tr\<Zprime>=tr @ [Event advVel] @ [State CAM]
        , advV\<Zprime> = maneuv(xvel, yvel)
        , (xvel,yvel)\<Zprime> = maneuv(xvel, yvel)
        , triggers\<Zprime> = {reqOCM}      
          ]"

zoperation HCMToCAM_1 =
  over LRE_Beh
  pre "st= HCM \<and> (-100> (fst(pos) + xvel) \<or> (fst(pos) + xvel) >100 \<or>  -100> (snd(pos) + yvel) \<or> (snd(pos) + yvel) >100)"
  update "[ st\<Zprime>= CAM
  		  , tr\<Zprime>=tr @ [Event advVel] @ [State CAM] 
        , advV\<Zprime> = maneuv(xvel, yvel)
        , (xvel,yvel)\<Zprime> = maneuv(xvel, yvel)
        , triggers\<Zprime> = {reqOCM}       
          ]"

zoperation MOMToCAM =
  over LRE_Beh
  pre "st= MOM \<and> CDA(pos,Obsts, (xvel,yvel))\<le>  MinSafeDist^2 \<and>dist(pos,Obsts)\<le> (MinSafeDist+5)^2 "
  update "[ st\<Zprime>= CAM
  		  , tr\<Zprime>=tr @ [Event advVel] @ [State CAM]
        , advV\<Zprime> = maneuv(xvel, yvel)
        , (xvel,yvel)\<Zprime> = maneuv(xvel, yvel)
        , triggers\<Zprime> = {reqOCM}      
          ]"

zoperation MOMToCAM_1 =
  over LRE_Beh
  pre "st= MOM \<and> (-100> (fst(pos) + xvel) \<or> (fst(pos) + xvel) >100 \<or>  -100> (snd(pos) + yvel) \<or> (snd(pos) + yvel) >100)"
  update "[ st\<Zprime>= CAM
  		  , tr\<Zprime>=tr @ [Event advVel] @ [State CAM]
        , advV\<Zprime> = maneuv(xvel, yvel)
        , (xvel,yvel)\<Zprime> = maneuv(xvel, yvel)
        , triggers\<Zprime> = {reqOCM}        
          ]"



zoperation CAMToCAM =
  over LRE_Beh
  pre "st= CAM \<and> CDA(pos,Obsts, (xvel,yvel))\<le>  MinSafeDist^2 \<and>dist(pos,Obsts)\<le>  (MinSafeDist+5)^2 "
  update "[ st\<Zprime>= CAM
  		  , tr\<Zprime>=tr @ [Event advVel] @ [State CAM]
        , advV\<Zprime> = maneuv(xvel, yvel)
        , (xvel,yvel)\<Zprime> = maneuv(xvel, yvel)
        , triggers\<Zprime> = {reqOCM}      
          ]"

zoperation CAMToCAM_1 =
  over LRE_Beh
  pre "st= CAM \<and>  (-100> (fst(pos) + xvel) \<or> (fst(pos) + xvel) >100 \<or>  -100> (snd(pos) + yvel) \<or> (snd(pos) + yvel) >100)"
  update "[ st\<Zprime>= CAM
  		  , tr\<Zprime>=tr @ [Event advVel] @ [State CAM]
        , advV\<Zprime> = maneuv(xvel, yvel)
        , (xvel,yvel)\<Zprime> = maneuv(xvel, yvel)
        , triggers\<Zprime> = {reqOCM}      
          ]"

zoperation CAMToOCM =
  over LRE_Beh
  pre "st= CAM \<and> CDA(pos,Obsts, (xvel,yvel))>  MinSafeDist^2"
  update "[ st\<Zprime>= OCM
  		  , tr\<Zprime>=tr @[Event advVel] @ [State OCM]
        , advV\<Zprime> = ZeroVel
        , (xvel,yvel)\<Zprime> = ZeroVel
        , triggers\<Zprime> = {reqMOM, reqVel}     
          ]"
        
zoperation CAMToOCM_1 =
  over LRE_Beh
  pre "st= CAM  "
  update "[ st\<Zprime>= OCM
  		  , tr\<Zprime>=tr @ [Event reqOCM] @ [State OCM]
        , triggers\<Zprime> = {reqMOM, reqVel}     
          ]"


definition Init :: "LRE_Beh subst" where
  [z_defs]:
  "Init = 
  [pos\<leadsto>(0,0),
xvel \<leadsto> 0,
yvel \<leadsto> 0,
advV \<leadsto> (0,0),
st \<leadsto> OCM,
tr  \<leadsto> [State OCM],   
 triggers \<leadsto>  {reqOCM}

]"

  



def_consts Velocities = "{(0,1),(0,-2), (2,0),(-4,0)}"
declare Velocities_def [z_defs]

def_consts MinSafeDist= "2"
declare MinSafeDist_def [z_defs]

def_consts HCMVel = "3"
declare HCMVel_def [z_defs]

def_consts MOMVel = "5"
declare MOMVel_def [z_defs]


def_consts ZeroVel = "(0,0)"
declare ZeroVel_def [z_defs]

def_consts SafeVel = "3"
declare SafeVel_def [z_defs]





subsection \<open> Structural Invariants \<close>

lemma Init_inv [hoare_lemmas]: "Init establishes LRE_Beh_inv"
  by (zpog_full; auto)

lemma InitialToOCM_inv [hoare_lemmas]: "InitialToOCM () preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma OCMToMOM_inv [hoare_lemmas]: "OCMToMOM() preserves LRE_Beh_inv"
  apply (zpog_full; auto)
 by (metis add_2_eq_Suc' cancel_ab_semigroup_add_class.add_diff_cancel_left' not_add_less1 nth_Cons_0 nth_Cons_Suc nth_append numeral_2_eq_2)+
  
lemma MOMToOCM_inv [hoare_lemmas]: "MOMToOCM () preserves LRE_Beh_inv"
  apply (zpog_full )
  apply (simp add: nth_append)
  done

lemma MOMToOCM_1_inv [hoare_lemmas]: "MOMToOCM_1 () preserves LRE_Beh_inv"
   by (zpog_full; auto)

lemma MOMToOCM_2_inv [hoare_lemmas]: "MOMToOCM_2 () preserves LRE_Beh_inv"
    apply (zpog_full)
   apply (simp add: nth_append)
  done

lemma HCMToOCM_inv [hoare_lemmas]: "HCMToOCM () preserves LRE_Beh_inv"
  apply (zpog_full)
  apply (metis One_nat_def Suc_eq_plus1 cancel_ab_semigroup_add_class.add_diff_cancel_left' not_add_less1 nth_Cons_0 nth_Cons_Suc nth_append)
  done

lemma HCMToOCM_1_inv [hoare_lemmas]: "HCMToOCM_1() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToHCM_inv [hoare_lemmas]: "MOMToHCM() preserves LRE_Beh_inv"
  apply (zpog_full )
by (metis One_nat_def Suc_eq_plus1 nth_Cons_0 nth_Cons_Suc nth_append_length_plus)


lemma HCMToMOM_inv [hoare_lemmas]: "HCMToMOM() preserves LRE_Beh_inv"
  apply (zpog_full )
 by (metis One_nat_def Suc_eq_plus1 Suc_pred cancel_ab_semigroup_add_class.add_diff_cancel_left' diff_less_Suc not_less_eq nth_Cons_0 nth_Cons_Suc nth_append)

  
lemma OCMToOCM_inv [hoare_lemmas]: "OCMToOCM (v) preserves LRE_Beh_inv"
  apply (zpog_full )
   apply (simp add: nth_append)
  by (simp add: nth_append)
  
  
lemma HCMToCAM_inv [hoare_lemmas]: "HCMToCAM() preserves LRE_Beh_inv"
  apply (zpog_full )
  by (metis One_nat_def Suc_eq_plus1 Suc_pred cancel_ab_semigroup_add_class.add_diff_cancel_left' diff_less_Suc not_less_eq nth_Cons_0 nth_Cons_Suc nth_append)

lemma HCMToCAM_1_inv [hoare_lemmas]: "HCMToCAM_1() preserves LRE_Beh_inv"
  apply (zpog_full )
  apply (metis One_nat_def Suc_eq_plus1 nth_Cons_0 nth_Cons_Suc nth_append_length_plus)
  by (simp add: nth_append)


lemma MOMToCAM_inv [hoare_lemmas]: "MOMToCAM() preserves LRE_Beh_inv"
   apply (zpog_full )
  by (metis One_nat_def Suc_eq_plus1 nth_Cons_0 nth_Cons_Suc nth_append_length_plus)

lemma MOMToCAM_1_inv [hoare_lemmas]: "MOMToCAM_1() preserves LRE_Beh_inv"
  apply (zpog_full )
  apply (simp add: nth_append)
  by (simp add: nth_append)


lemma CAMToCAM_inv [hoare_lemmas]: "CAMToCAM () preserves LRE_Beh_inv"
  apply (zpog_full )
  by (metis One_nat_def Suc_eq_plus1 nth_Cons_0 nth_Cons_Suc nth_append_length_plus)

lemma CAMToCAM_1_inv [hoare_lemmas]: "CAMToCAM_1 () preserves LRE_Beh_inv"
  apply (zpog_full )
  apply (simp add: nth_append)
  by (simp add: nth_append)


lemma CAMToOCM_inv [hoare_lemmas]: "CAMToOCM () preserves LRE_Beh_inv"
  apply (zpog_full )
  apply (metis One_nat_def Suc_eq_plus1 nth_Cons_0 nth_Cons_Suc nth_append_length_plus)
  done

lemma CAMToOCM_1_inv [hoare_lemmas]: "CAMToOCM_1() preserves LRE_Beh_inv"
  apply (zpog_full )
   apply (metis append_Cons append_Nil append_assoc length_append_singleton nth_append_length)
  done

lemma Move_inv [hoare_lemmas]: "Move() preserves LRE_Beh_inv"
  by (zpog_full; auto)


subsection \<open> Safety Requirements \<close>

zmachine LRE_BehMachine =
  init   "  [pos\<leadsto>(0,0),
xvel \<leadsto> 0,
yvel \<leadsto> 0,
advV \<leadsto> (0,0),
st \<leadsto> initial,
tr  \<leadsto> [State initial],
   triggers \<leadsto>  {reqOCM}
]"
  invariant LRE_Beh_inv
  operations    InitialToOCM  OCMToOCM
 OCMToMOM MOMToOCM MOMToOCM_1  MOMToOCM_2 HCMToOCM HCMToOCM_1 MOMToHCM  HCMToMOM  
HCMToCAM HCMToCAM_1  MOMToCAM MOMToCAM_1  CAMToCAM CAMToCAM_1  CAMToOCM CAMToOCM_1 
  
lemma LRE_Beh_deadlock_free: " deadlock_free LRE_BehMachine" 
  apply deadlock_free
  by (metis St.exhaust_disc)


end

