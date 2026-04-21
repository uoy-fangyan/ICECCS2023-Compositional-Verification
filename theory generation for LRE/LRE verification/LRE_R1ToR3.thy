theory LRE_R1ToR3
imports "Z_Machines.Z_Machine"
begin

notation undefined ("???")

subsection \<open> Introduction \<close>

text \<open> This theory file is to model the LRE_Beh state machine in Z Machine notations.\<close>

datatype ('s, 'e) tag =
  State (ofState: 's) | Event (ofEvent: 'e)

abbreviation "is_Event x \<equiv> \<not> is_State x"

type_synonym ('s, 'e) rctrace = "('s, 'e) tag list"

definition wf_rcstore :: "('s, 'e) rctrace \<Rightarrow> 's \<Rightarrow> 's option \<Rightarrow> bool" where
[z_defs]: "wf_rcstore tr st final =  (
     length(tr) > 0 
   \<and> tr ! ((length tr) -1) = State st 
   \<and> ( final \<noteq> None \<longrightarrow> (\<forall>i<length tr. tr ! i = State (the final) \<longrightarrow> i= (length tr) -1)) 
   \<and> (filter is_State tr) ! (length (filter is_State tr) -1) = State  st)"


subsection \<open> type definition \<close>

enumtype St = OCM | MOM | HCM | CAM | initial 


enumtype Evt = advVel | reqHCM | reqOCM | reqMOM | endTask | reqVel 


type_synonym coord="real\<times>real"

record Obstacle =
  obspos :: coord
  id :: nat

consts Obsts :: " coord list"

consts Positions::"(coord) set"

consts Velocities:: "(real\<times>real) set"
consts ReqV:: "(real\<times>real) set"

consts HCMVel:: "real"

consts MOMVel:: "real"

consts MinSafeDist :: "real"

consts Opez_min:: "coord"
consts Opez_max:: "coord"
consts SafeVel :: "real"
consts ZeroVel:: "coord"

text \<open> function definition \<close>

fun inOPEZ:: "coord\<Rightarrow> bool"
  where "inOPEZ (x,y) = ( x\<ge> fst Opez_min \<and> x< fst Opez_max \<and> y\<ge>snd Opez_min \<and> y< snd Opez_max)"

fun single_dist:: " coord \<times> coord  \<Rightarrow> real"
  where "single_dist((x,y), (m,n)) =(x-m)^2+ (y-n)^2"

fun dist:: " coord \<times> (coord list) \<Rightarrow> real"
  where 
"dist((x,y),[]) = 200^2+ 200^2" |
 " dist((x,y), g#gs) =( if  single_dist((x,y),g) \<le> dist ((x,y),gs) then single_dist((x,y),g) else dist ((x,y),gs))"

fun obst_index:: "coord  \<times> (coord list) \<Rightarrow> nat"
  where
"obst_index ((x,y), [])=100 " |
 "obst_index ((x,y), g#gs)= (if single_dist ((x,y),g) = dist ((x,y),g#gs) then 0 else  (obst_index ((x,y), gs)+1))"


fun abslt:: "real\<Rightarrow> real"
  where "abslt(x) = (if x\<ge>0 then x else -x)"

fun closestObs_xpos :: "coord \<times> (coord list) \<Rightarrow> real"
  where "closestObs_xpos((xp,yp),[]) = 1000000"|
        "closestObs_xpos((xp,yp),g#gs) = fst ((g#gs) ! obst_index((xp,yp), g#gs))"

fun closestObs_ypos :: "coord \<times> (coord list) \<Rightarrow> real"
  where "closestObs_ypos((xp,yp),[]) = 1000000"|
        "closestObs_ypos((xp,yp),g#gs) = snd ((g#gs) ! obst_index((xp,yp), g#gs))"


fun CDA :: " coord \<times> (coord list)\<times> (real \<times> real) \<Rightarrow> real"
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


fun maneuv :: "real\<times> real \<Rightarrow> real\<times> real"
  where "maneuv(x,y) = (y,-x)"


fun setVel :: "(real \<times> real) \<times> real   \<Rightarrow>   (real \<times> real) " 
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

instantiation real :: default
begin
definition "default_real = (0::real)"
instance ..
end

zstore LRE_Beh =
  pos:: "coord"
  xvel :: "real"
  yvel :: "real"
  reqV:: "real \<times> real"
  advV::"real \<times> real"
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
  pre "st= MOM "
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
  params reqV_input \<in> " ReqV"
  pre "st= OCM "
  update "[ st\<Zprime>= OCM
  		  , tr\<Zprime>=tr @ [Event reqVel] @ [Event advVel] @[State OCM] 
        ,reqV\<Zprime> = reqV_input      
        , advV\<Zprime> = reqV_input  
        , (xvel,yvel)\<Zprime> = reqV_input
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
  pre "st= CAM "
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
reqV\<leadsto> (0,0),
   st \<leadsto> initial,
   tr  \<leadsto> [State initial],
   triggers \<leadsto>  {reqOCM}
   ]"
(*
zmachine LRE_BehMachine =
  init Init
  invariant LRE_Beh_inv
  operations    InitialToOCM  OCMToOCM
 OCMToMOM MOMToOCM MOMToOCM_1  MOMToOCM_2 HCMToOCM HCMToOCM_1 MOMToHCM  HCMToMOM HCMToCAM HCMToCAM_1  MOMToCAM MOMToCAM_1  CAMToCAM CAMToCAM_1  CAMToOCM CAMToOCM_1 
*)
  
def_consts Velocities = "{(0,1),(0,-2), (2,0),(-4,0)}"
declare Velocities_def [z_defs]

def_consts MinSafeDist= "2"
declare MinSafeDist_def [z_defs]

def_consts HCMVel = "0.3"
declare HCMVel_def [z_defs]

def_consts MOMVel = "0.5"
declare MOMVel_def [z_defs]


def_consts ZeroVel = "(0,0)"
declare ZeroVel_def [z_defs]

def_consts SafeVel = "0.3"
declare SafeVel_def [z_defs]





method zpog uses add = 
  (hoare_wlp add: z_defs add; (clarify)?; 
   expr_taut; 
   ((clarsimp del: notI)?; 
    (((erule conjE | rule conjI | erule disjE | rule impI); (clarsimp del: notI)?)+)?))
method zpog_full uses add = (zpog add: z_locale_defs add)


lemma prod_var_decomp: " get\<^bsub>x\<^esub> s= ( get\<^bsub>var_fst x\<^esub> s,  get\<^bsub>var_snd x\<^esub> s)"
  by (simp add: lens_defs)


subsection \<open> Structural Invariants \<close>

lemma Init_inv [hoare_lemmas]: "Init establishes LRE_Beh_inv"
  by (zpog_full; auto)

lemma InitialToOCM_inv [hoare_lemmas]: "InitialToOCM () preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma OCMToMOM_inv [hoare_lemmas]: "OCMToMOM() preserves LRE_Beh_inv"
  apply (zpog_full; auto)
  apply (metis add_2_eq_Suc' cancel_ab_semigroup_add_class.add_diff_cancel_left' not_add_less1 nth_Cons_0 nth_Cons_Suc nth_append numeral_2_eq_2)
  apply (metis add_2_eq_Suc' cancel_ab_semigroup_add_class.add_diff_cancel_left' not_add_less1 nth_Cons_0 nth_Cons_Suc nth_append numeral_2_eq_2)
  apply (metis add_2_eq_Suc' cancel_ab_semigroup_add_class.add_diff_cancel_left' not_add_less1 nth_Cons_0 nth_Cons_Suc nth_append numeral_2_eq_2)
  by (metis add_2_eq_Suc' cancel_ab_semigroup_add_class.add_diff_cancel_left' not_add_less1 nth_Cons_0 nth_Cons_Suc nth_append numeral_2_eq_2)

lemma MOMToOCM_inv [hoare_lemmas]: "MOMToOCM () preserves LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (simp add: nth_append)


lemma MOMToOCM_1_inv [hoare_lemmas]: "MOMToOCM_1 () preserves LRE_Beh_inv"
   by (zpog_full; auto)

lemma MOMToOCM_2_inv [hoare_lemmas]: "MOMToOCM_2 () preserves LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (simp add: nth_append)

  
lemma HCMToOCM_inv [hoare_lemmas]: "HCMToOCM () preserves LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (metis One_nat_def Suc_eq_plus1 Suc_n_not_le_n cancel_ab_semigroup_add_class.add_diff_cancel_left' nat_less_le nth_Cons_0 nth_Cons_Suc nth_append)

lemma HCMToOCM_1_inv [hoare_lemmas]: "HCMToOCM_1() preserves LRE_Beh_inv"
  by (zpog_full; auto)
  
lemma MOMToHCM_inv [hoare_lemmas]: "MOMToHCM() preserves LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (metis append.assoc append_Cons append_Nil length_append_singleton nth_append_length)


lemma HCMToMOM_inv [hoare_lemmas]: "HCMToMOM() preserves LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (metis One_nat_def add_diff_cancel_right' not_add_less2 nth_Cons_0 nth_Cons_Suc nth_append plus_1_eq_Suc)

  
lemma OCMToOCM_inv [hoare_lemmas]: "OCMToOCM (v) preserves LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (simp add: nth_append)

  
  
lemma HCMToCAM_inv [hoare_lemmas]: "HCMToCAM() preserves LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (metis append.left_neutral append_Cons append_assoc length_append_singleton nth_append_length)

lemma HCMToCAM_1_inv [hoare_lemmas]: "HCMToCAM_1() preserves LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  apply (simp add: nth_append)
  by (simp add: nth_append)

lemma MOMToCAM_inv [hoare_lemmas]: "MOMToCAM() preserves LRE_Beh_inv"
   apply (zpog_full add: prod_var_decomp)
  by (simp add: nth_append)

lemma MOMToCAM_1_inv [hoare_lemmas]: "MOMToCAM_1() preserves LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  apply (simp add: nth_append)
  by (simp add: nth_append)


lemma CAMToCAM_inv [hoare_lemmas]: "CAMToCAM () preserves LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (metis One_nat_def add_diff_cancel_right' not_add_less2 nth_Cons_0 nth_Cons_Suc nth_append plus_1_eq_Suc)

lemma CAMToCAM_1_inv [hoare_lemmas]: "CAMToCAM_1 () preserves LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  apply (simp add: nth_append)
  by (simp add: nth_append)


lemma CAMToOCM_inv [hoare_lemmas]: "CAMToOCM () preserves LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (simp add: nth_append)


  
lemma CAMToOCM_1_inv [hoare_lemmas]: "CAMToOCM_1() preserves LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (metis append_Cons append_Nil append_assoc length_append_singleton nth_append_length)
 





subsection \<open> Safety Requirements \<close>


zexpr R1 is
"\<forall> i < length (filter is_State tr)-1 . (filter is_State tr) ! i= State CAM \<longrightarrow> (filter is_State tr) ! (i+1) \<in> {State OCM, State CAM}"
lemma "Init establishes R1"
  by zpog_full

lemma  "InitialToOCM () preserves R1  under LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (metis (no_types, lifting) Nat.lessE Suc_less_eq Suc_pred nth_append nth_append_length zero_less_Suc)

 
lemma "OCMToMOM() preserves  R1 under LRE_Beh_inv"
 apply (zpog_full add: prod_var_decomp)
  by (metis (no_types, lifting) Nat.lessE One_nat_def St.distinct_disc(6) Suc_lessI diff_Suc_1 nth_append tag.inject(1))
  
lemma  "MOMToOCM() preserves  R1 under LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (metis (no_types, opaque_lifting) Nat.lessE One_nat_def St.distinct_disc(12) Suc_lessI diff_Suc_1 nth_append tag.inject(1))


 
lemma  "HCMToOCM () preserves R1 under LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (metis (no_types, opaque_lifting) Nat.lessE One_nat_def St.distinct_disc(15) Suc_lessI diff_Suc_1 nth_append tag.inject(1))


lemma  "MOMToHCM() preserves  R1 under LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (metis (no_types, lifting) Nat.lessE One_nat_def St.distinct_disc(11) Suc_less_eq diff_Suc_1 nth_append tag.inject(1))


lemma  "MOMToOCM_1() preserves  R1 under LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  apply (simp add: nth_append)
  apply (metis Suc_less_eq Suc_pred length_greater_0_conv list.size(3) not_less_zero)
  by (metis (no_types, opaque_lifting) St.simps(12) Suc_lessI add.right_neutral add_Suc_right cancel_comm_monoid_add_class.diff_zero diff_Suc_Suc less_diff_conv nth_append tag.inject(1))

 
    
lemma  "HCMToOCM_1() preserves R1 under LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  apply (metis (no_types, lifting) Nat.lessE Suc_less_eq Suc_pred nth_append nth_append_length zero_less_Suc)
  by (metis (no_types, lifting) Nat.lessE Suc_less_eq Suc_pred nth_append nth_append_length zero_less_Suc)

  
lemma  "HCMToMOM() preserves R1 under LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (smt (verit, ccfv_threshold) Nat.lessE St.simps(16) Suc_less_eq Suc_pred diff_Suc_1 length_greater_0_conv list.size(3) not_less_zero nth_append tag.inject(1))

  

  
lemma  "OCMToOCM (v) preserves R1 under LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (metis (no_types, opaque_lifting) Nat.lessE One_nat_def St.simps(6) Suc_lessI diff_Suc_1 nth_append tag.inject(1))


 

lemma  "MOMToOCM_2() preserves R1 under LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (metis (no_types, opaque_lifting) Nat.lessE One_nat_def St.simps(12) Suc_lessI diff_Suc_1 nth_append tag.inject(1))



lemma  "HCMToCAM() preserves R1 under LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (metis (no_types, lifting) Nat.lessE Suc_less_eq Suc_pred nth_append nth_append_length zero_less_Suc)



lemma  "MOMToCAM() preserves  R1 under LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (metis (no_types, lifting) Nat.lessE Suc_less_eq Suc_pred nth_append nth_append_length zero_less_Suc)



lemma  "CAMToOCM () preserves R1 under LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (metis (no_types, lifting) Nat.lessE Suc_less_eq Suc_pred nth_append nth_append_length zero_less_Suc)


lemma  "CAMToOCM_1() preserves  R1 under LRE_Beh_inv"
  apply (zpog_full add: prod_var_decomp)
  by (metis (no_types, lifting) Nat.lessE Suc_less_eq Suc_pred nth_append nth_append_length zero_less_Suc)





zexpr R2  is 
"st = MOM \<longrightarrow> (tr ! (length tr-2) = Event advVel \<and> (xvel^2 + yvel^2 < 0.36) \<and> (xvel^2 + yvel^2 >0.16) ) "

lemma  "Init establishes  R2  "
  by  zpog_full

lemma  "InitialToOCM () preserves  R2  under LRE_Beh_inv"
  by  zpog_full
  

lemma "OCMToMOM() preserves  R2  under LRE_Beh_inv"
  apply  zpog_full
  apply (metis One_nat_def Suc_eq_plus1 nth_Cons_0 nth_Cons_Suc nth_append_length_plus)
  apply (simp add: power_divide)
  apply (simp add: nth_append power_divide)
  by (simp add: nth_append power_divide)
 


lemma  "MOMToOCM() preserves R2  under LRE_Beh_inv"
  by  zpog_full


lemma  "MOMToOCM_1() preserves  R2  under LRE_Beh_inv"
  by  zpog_full

lemma  "MOMToOCM_2() preserves R2  under LRE_Beh_inv"
  by  zpog_full

lemma  "HCMToOCM () preserves R2  under LRE_Beh_inv"
  by  zpog_full
  
lemma  "HCMToOCM_1() preserves R2  under LRE_Beh_inv"
  by  zpog_full

lemma  "MOMToHCM() preserves R2  under LRE_Beh_inv"
  by  zpog_full

lemma  "HCMToMOM() preserves R2  under LRE_Beh_inv"
  apply  zpog_full
  apply (simp add: power_divide)
  apply (simp add: power_divide)
  apply (simp add: power_one_over)
  by (simp add: power_one_over)

lemma  "OCMToOCM (v) preserves R2  under LRE_Beh_inv"
  by  zpog_full
  
 
lemma  "HCMToCAM() preserves R2  under LRE_Beh_inv"
  by  zpog_full

lemma  "HCMToCAM_1() preserves R2  under LRE_Beh_inv"
  by  zpog_full

lemma  "MOMToCAM() preserves  R2  under LRE_Beh_inv"
  by  zpog_full

lemma  "MOMToCAM_1() preserves  R2  under LRE_Beh_inv"
  by  zpog_full

lemma  "CAMToCAM() preserves R2  under LRE_Beh_inv"
  by  zpog_full

lemma  "CAMToCAM_1() preserves R2  under LRE_Beh_inv"
  by  zpog_full

lemma  "CAMToOCM () preserves R2  under LRE_Beh_inv"
  by  zpog_full

lemma  "CAMToOCM_1() preserves  R2  under LRE_Beh_inv"
  by  zpog_full

lemma "Move() preserves R2  under LRE_Beh_inv"
  by  zpog_full







zexpr R3 is 
"st\<noteq>OCM \<longrightarrow>reqOCM \<in> triggers"

lemma  "Init establishes  R3 "
  by  zpog_full

lemma  "InitialToOCM () preserves  R3 under LRE_Beh_inv"
  by  zpog_full
  

lemma "OCMToMOM() preserves  R3 under LRE_Beh_inv"
  by  zpog_full


lemma  "MOMToOCM() preserves R3 under LRE_Beh_inv"
  by  zpog_full


lemma  "MOMToOCM_1() preserves  R3 under LRE_Beh_inv"
  by  zpog_full

lemma  "MOMToOCM_2() preserves R3 under LRE_Beh_inv"
  by  zpog_full

lemma  "HCMToOCM () preserves R3 under LRE_Beh_inv"
  by  zpog_full
  
lemma  "HCMToOCM_1() preserves R3 under LRE_Beh_inv"
  by  zpog_full

lemma  "MOMToHCM() preserves R3 under LRE_Beh_inv"
  by  zpog_full

lemma  "HCMToMOM() preserves R3 under LRE_Beh_inv"
  by  zpog_full

lemma  "OCMToOCM (v) preserves R3 under LRE_Beh_inv"
  by  zpog_full
  
 
lemma  "HCMToCAM() preserves R3 under LRE_Beh_inv"
  by  zpog_full

lemma  "HCMToCAM_1() preserves R3 under LRE_Beh_inv"
  by  zpog_full

lemma  "MOMToCAM() preserves  R3 under LRE_Beh_inv"
  by  zpog_full

lemma  "MOMToCAM_1() preserves  R3 under LRE_Beh_inv"
  by  zpog_full

lemma  "CAMToCAM() preserves R3 under LRE_Beh_inv"
  by  zpog_full

lemma  "CAMToCAM_1() preserves R3 under LRE_Beh_inv"
  by  zpog_full

lemma  "CAMToOCM () preserves R3 under LRE_Beh_inv"
  by  zpog_full

lemma  "CAMToOCM_1() preserves  R3 under LRE_Beh_inv"
  by  zpog_full

lemma "Move() preserves R3 under LRE_Beh_inv"
  by  zpog_full


end

