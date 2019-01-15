(*  Title:      HOL/MicroJava/BV/Correct.thy

    Author:     Cornelia Pusch, Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen

The invariant for the type safety proof.
*)
(*
    Expanded to include statics and class initialization by Susannah Mansky
    2018, UIUC
*)

section {* BV Type Safety Invariant *}

theory BVConform
imports BVSpec "../JVM/JVMExec" "../Common/Conform"
begin


definition confT :: "'c prog \<Rightarrow> heap \<Rightarrow> val \<Rightarrow> ty err \<Rightarrow> bool" 
    ("_,_ \<turnstile> _ :\<le>\<^sub>\<top> _" [51,51,51,51] 50)
where
  "P,h \<turnstile> v :\<le>\<^sub>\<top> E \<equiv> case E of Err \<Rightarrow> True | OK T \<Rightarrow> P,h \<turnstile> v :\<le> T"

notation (ASCII)
  confT  ("_,_ |- _ :<=T _" [51,51,51,51] 50)

abbreviation
  confTs :: "'c prog \<Rightarrow> heap \<Rightarrow> val list \<Rightarrow> ty\<^sub>l \<Rightarrow> bool" 
      ("_,_ \<turnstile> _ [:\<le>\<^sub>\<top>] _" [51,51,51,51] 50) where
  "P,h \<turnstile> vs [:\<le>\<^sub>\<top>] Ts \<equiv> list_all2 (confT P h) vs Ts"

notation (ASCII)
  confTs  ("_,_ |- _ [:<=T] _" [51,51,51,51] 50)

(* HERE: MOVE*)
abbreviation Called_set :: "instr set" where
"Called_set \<equiv> {i. \<exists>C. i = New C} \<union> {i. \<exists>C M n. i = Invokestatic C M n}
                 \<union> {i. \<exists>C F D. i = Getstatic C F D} \<union> {i. \<exists>C F D. i = Putstatic C F D}"

fun Called_context :: "jvm_prog \<Rightarrow> cname \<Rightarrow> instr \<Rightarrow> bool" where
"Called_context P C\<^sub>0 (New C') = (C\<^sub>0=C')" |
"Called_context P C\<^sub>0 (Getstatic C F D) =  ((C\<^sub>0=D) \<and> (\<exists>t. P \<turnstile> C has F,Static:t in D))" |
"Called_context P C\<^sub>0 (Putstatic C F D) = ((C\<^sub>0=D) \<and> (\<exists>t. P \<turnstile> C has F,Static:t in D))" |
"Called_context P C\<^sub>0 (Invokestatic C M n)
   = (\<exists>Ts T m D. (C\<^sub>0=D) \<and> P \<turnstile> C sees M,Static:Ts \<rightarrow> T = m in D)" |
"Called_context P _ _ = False"

lemma Called_context_Called_set:
 "Called_context P D i \<Longrightarrow> i \<in> Called_set" by(cases i, auto)

(* HERE: MOVE *)
fun valid_ics :: "jvm_prog \<Rightarrow> heap \<Rightarrow> sheap \<Rightarrow> cname \<times> mname \<times> pc \<times> init_call_status \<Rightarrow> bool"
  ("_,_,_ \<turnstile>\<^sub>i _" [51,51,51,51] 50) where
"valid_ics P h sh (C,M,pc,Calling C' Cs)
 = (let ins = instrs_of P C M in Called_context P (last (C'#Cs)) (ins!pc)
    \<and> is_class P C')" |
"valid_ics P h sh (C,M,pc,Throwing Cs a)
 =(let ins = instrs_of P C M in \<exists>C1. Called_context P C1 (ins!pc)
    \<and> (\<exists>obj. h a = Some obj))" |
"valid_ics P h sh (C,M,pc,Called Cs)
 = (let ins = instrs_of P C M
    in \<exists>C1 sobj. Called_context P C1 (ins!pc) \<and> sh C1 = Some sobj)" |
"valid_ics P _ _ _ = True"

definition conf_f  :: "jvm_prog \<Rightarrow> heap \<Rightarrow> sheap \<Rightarrow> ty\<^sub>i \<Rightarrow> bytecode \<Rightarrow> frame \<Rightarrow> bool"
where
  "conf_f P h sh \<equiv> \<lambda>(ST,LT) is (stk,loc,C,M,pc,ics).
  P,h \<turnstile> stk [:\<le>] ST \<and> P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT \<and> pc < size is \<and> P,h,sh \<turnstile>\<^sub>i (C,M,pc,ics)"

lemma conf_f_def2:
  "conf_f P h sh (ST,LT) is (stk,loc,C,M,pc,ics) \<equiv>
  P,h \<turnstile> stk [:\<le>] ST \<and> P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT \<and> pc < size is \<and> P,h,sh \<turnstile>\<^sub>i (C,M,pc,ics)"
  by (simp add: conf_f_def)

primrec conf_fs :: "[jvm_prog,heap,sheap,ty\<^sub>P,cname,mname,nat,ty,frame list] \<Rightarrow> bool"
where
  "conf_fs P h sh \<Phi> C\<^sub>0 M\<^sub>0 n\<^sub>0 T\<^sub>0 [] = True"
| "conf_fs P h sh \<Phi> C\<^sub>0 M\<^sub>0 n\<^sub>0 T\<^sub>0 (f#frs) =
  (let (stk,loc,C,M,pc,ics) = f in
  (\<exists>ST LT b Ts T mxs mxl\<^sub>0 is xt.
    \<Phi> C M ! pc = Some (ST,LT) \<and> 
    (P \<turnstile> C sees M,b:Ts \<rightarrow> T = (mxs,mxl\<^sub>0,is,xt) in C) \<and>
    ((\<exists>D Ts' T' m D'. M\<^sub>0 \<noteq> clinit \<and> ics = No_ics \<and>
       is!pc = Invoke M\<^sub>0 n\<^sub>0 \<and> ST!n\<^sub>0 = Class D \<and>
       P \<turnstile> D sees M\<^sub>0,NonStatic:Ts' \<rightarrow> T' = m in D' \<and> P \<turnstile> C\<^sub>0 \<preceq>\<^sup>* D' \<and> P \<turnstile> T\<^sub>0 \<le> T') \<or>
     (\<exists>D Ts' T' m. M\<^sub>0 \<noteq> clinit \<and> ics = No_ics \<and>
       is!pc = Invokestatic D M\<^sub>0 n\<^sub>0 \<and>
       P \<turnstile> D sees M\<^sub>0,Static:Ts' \<rightarrow> T' = m in C\<^sub>0 \<and> P \<turnstile> T\<^sub>0 \<le> T') \<or>
     (M\<^sub>0 = clinit \<and> (\<exists>Cs. ics = Called Cs))) \<and>
    conf_f P h sh (ST, LT) is f \<and> conf_fs P h sh \<Phi> C M (size Ts) T frs))"

fun ics_classes :: "init_call_status \<Rightarrow> cname list" where
"ics_classes (Calling C Cs) = Cs" |
"ics_classes (Throwing Cs a) = Cs" |
"ics_classes (Called Cs) = Cs" |
"ics_classes _ = []"

fun frame_clinit_classes :: "frame \<Rightarrow> cname list" where
"frame_clinit_classes (stk,loc,C,M,pc,ics) = (if M=clinit then [C] else []) @ ics_classes ics"

abbreviation clinit_classes :: "frame list \<Rightarrow> cname list" where
"clinit_classes frs \<equiv> concat (map frame_clinit_classes frs)"

(* HERE: MOVE? *)
definition distinct_clinit :: "frame list \<Rightarrow> bool" where
"distinct_clinit frs \<equiv> distinct (clinit_classes frs)"

definition conf_clinit :: "jvm_prog \<Rightarrow> sheap \<Rightarrow> frame list \<Rightarrow> bool" where
"conf_clinit P sh frs
   \<equiv> distinct_clinit frs \<and>
      (\<forall>C \<in> set(clinit_classes frs). is_class P C \<and> (\<exists>sfs. sh C = Some(sfs, Processing)))"

lemma conf_clinit_Cons:
assumes "conf_clinit P sh (f#frs)"
shows "conf_clinit P sh frs"
proof -
  from assms have dist: "distinct_clinit (f#frs)"
   by(cases "curr_method f = clinit", auto simp: conf_clinit_def)
  then have dist': "distinct_clinit frs" by(simp add: distinct_clinit_def)

  with assms show ?thesis by(cases frs; fastforce simp: conf_clinit_def)
qed

(* HERE: may want to generalize *)
lemma conf_clinit_Cons_Cons:
 "conf_clinit P sh (f'#f#frs) \<Longrightarrow> conf_clinit P sh (f'#frs)"
 by(auto simp: conf_clinit_def distinct_clinit_def)

lemma conf_clinit_diff:
assumes "conf_clinit P sh ((stk,loc,C,M,pc,ics)#frs)"
shows "conf_clinit P sh ((stk',loc',C,M,pc',ics)#frs)"
using assms by(cases "M = clinit", simp_all add: conf_clinit_def distinct_clinit_def)

lemma conf_clinit_diff':
assumes "conf_clinit P sh ((stk,loc,C,M,pc,ics)#frs)"
shows "conf_clinit P sh ((stk',loc',C,M,pc',No_ics)#frs)"
using assms by(cases "M = clinit", simp_all add: conf_clinit_def distinct_clinit_def)

lemma conf_clinit_Called_Throwing:
 "conf_clinit P sh ((stk', loc', C', clinit, pc', ics') # (stk, loc, C, M, pc, Called Cs) # fs)
  \<Longrightarrow> conf_clinit P sh ((stk, loc, C, M, pc, Throwing (C' # Cs) xcp) # fs)"
 by(simp add: conf_clinit_def distinct_clinit_def)

lemma conf_clinit_Throwing:
 "conf_clinit P sh ((stk, loc, C, M, pc, Throwing (C'#Cs) xcp) # fs)
  \<Longrightarrow> conf_clinit P sh ((stk, loc, C, M, pc, Throwing Cs xcp) # fs)"
 by(simp add: conf_clinit_def distinct_clinit_def)

lemma conf_clinit_Called:
 "\<lbrakk> conf_clinit P sh ((stk, loc, C, M, pc, Called (C'#Cs)) # frs);
    P \<turnstile> C' sees clinit,Static: [] \<rightarrow> Void=(mxs',mxl',ins',xt') in C' \<rbrakk>
  \<Longrightarrow> conf_clinit P sh (create_init_frame P C' # (stk, loc, C, M, pc, Called Cs) # frs)"
 by(simp add: conf_clinit_def distinct_clinit_def)

lemma conf_clinit_Cons_nclinit:
assumes "conf_clinit P sh frs" and nclinit: "M \<noteq> clinit"
shows "conf_clinit P sh ((stk, loc, C, M, pc, No_ics) # frs)"
proof -
  from nclinit
  have "clinit_classes ((stk, loc, C, M, pc, No_ics) # frs) = clinit_classes frs" by simp
  with assms show ?thesis by(simp add: conf_clinit_def distinct_clinit_def)
qed

lemma conf_clinit_Invoke:
assumes "conf_clinit P sh ((stk, loc, C, M, pc, ics) # frs)" and "M' \<noteq> clinit"
shows "conf_clinit P sh ((stk', loc', C', M', pc', No_ics) # (stk, loc, C, M, pc, No_ics) # frs)"
 using assms conf_clinit_Cons_nclinit conf_clinit_diff' by auto

(*************************)

definition correct_state :: "[jvm_prog,ty\<^sub>P,jvm_state] \<Rightarrow> bool"  ("_,_ \<turnstile> _ \<surd>"  [61,0,0] 61)
where
  "correct_state P \<Phi> \<equiv> \<lambda>(xp,h,frs,sh).
  case xp of
     None \<Rightarrow> (case frs of
             [] \<Rightarrow> True
             | (f#fs) \<Rightarrow> P\<turnstile> h\<surd> \<and> P,h\<turnstile>\<^sub>s sh\<surd> \<and> conf_clinit P sh frs \<and>
             (let (stk,loc,C,M,pc,ics) = f
              in \<exists>b Ts T mxs mxl\<^sub>0 is xt \<tau>.
                    (P \<turnstile> C sees M,b:Ts\<rightarrow>T = (mxs,mxl\<^sub>0,is,xt) in C) \<and>
                    \<Phi> C M ! pc = Some \<tau> \<and>
                    conf_f P h sh \<tau> is f \<and> conf_fs P h sh \<Phi> C M (size Ts) T fs))
  | Some x \<Rightarrow> frs = []" 

notation
  correct_state  ("_,_ |- _ [ok]"  [61,0,0] 61)

lemma correct_state_Cons:
assumes cr: "P,\<Phi> |- (xp,h,f#frs,sh) [ok]"
shows "P,\<Phi> |- (xp,h,frs,sh) [ok]"
proof -
  from cr have dist: "conf_clinit P sh (f#frs)"
   by(simp add: correct_state_def)
  then have "conf_clinit P sh frs" by(rule conf_clinit_Cons)

  with cr show ?thesis by(cases frs; fastforce simp: correct_state_def)
qed

(* HERE: MOVE *) (* HERE: currently unused -- and with conf_clinit, now much more obvious *) (*
lemma clinit_class_Proc:
 "\<lbrakk> P,\<Phi> |- (xp,h,f#frs,sh) [ok];
    C\<^sub>0 \<in> set(clinit_classes frs) \<rbrakk>
 \<Longrightarrow> \<exists>sfs. sh C\<^sub>0 = \<lfloor>(sfs, Processing)\<rfloor>"
proof(induct frs arbitrary: f)
  case Nil then show ?case by(cases "curr_method f = clinit", auto simp: correct_state_def conf_f_def2)
next
  case (Cons f' frs')
  with correct_state_Cons[OF Cons.prems(1)] have
   cr': "P,\<Phi> |- (xp,h,f'#frs',sh) [ok]" by simp

  show ?case
  proof(cases "C\<^sub>0 \<in> set(frame_clinit_classes f')")
    case False with cr' Cons show ?thesis by simp
  next
    case True with Cons.prems(1) show ?thesis
      by(auto simp: correct_state_def conf_f_def2 conf_clinit_def)
  qed
qed *)

(* HERE: MOVE *) (* HERE: not used
(* if C is not in a current clinit state, then C has no current clinit frame *)
lemma nclinit_current:
assumes cr: "P,\<Phi> |- (xp,h,(stk,loc,C,M,pc,ics)#frs,sh) [ok]"
    and ncc: "\<not>clinit_current sh C\<^sub>0 clinit"
shows "distinct (C\<^sub>0#clinit_classes ((stk,loc,C,M,pc,ics)#frs))"
proof -
  from cr have dist: "distinct_clinit ((stk,loc,C,M,pc,ics)#frs)"
    by(cases "M=clinit"; clarsimp simp: correct_state_def)
  { assume "C\<^sub>0 \<in> set(clinit_classes ((stk,loc,C,M,pc,ics)#frs))"
    with clinit_class_Proc[OF cr] ncc have "False" by auto
  }
  then have "C\<^sub>0 \<notin> set(clinit_classes ((stk,loc,C,M,pc,ics)#frs))" by fast
  with dist show ?thesis by simp
qed *)

subsection {* Values and @{text "\<top>"} *}

lemma confT_Err [iff]: "P,h \<turnstile> x :\<le>\<^sub>\<top> Err" 
  by (simp add: confT_def)

lemma confT_OK [iff]:  "P,h \<turnstile> x :\<le>\<^sub>\<top> OK T = (P,h \<turnstile> x :\<le> T)"
  by (simp add: confT_def)

lemma confT_cases:
  "P,h \<turnstile> x :\<le>\<^sub>\<top> X = (X = Err \<or> (\<exists>T. X = OK T \<and> P,h \<turnstile> x :\<le> T))"
  by (cases X) auto

lemma confT_hext [intro?, trans]:
  "\<lbrakk> P,h \<turnstile> x :\<le>\<^sub>\<top> T; h \<unlhd> h' \<rbrakk> \<Longrightarrow> P,h' \<turnstile> x :\<le>\<^sub>\<top> T"
  by (cases T) (blast intro: conf_hext)+

lemma confT_widen [intro?, trans]:
  "\<lbrakk> P,h \<turnstile> x :\<le>\<^sub>\<top> T; P \<turnstile> T \<le>\<^sub>\<top> T' \<rbrakk> \<Longrightarrow> P,h \<turnstile> x :\<le>\<^sub>\<top> T'"
  by (cases T', auto intro: conf_widen)


subsection {* Stack and Registers *}

lemmas confTs_Cons1 [iff] = list_all2_Cons1 [of "confT P h"] for P h

lemma confTs_confT_sup:
  "\<lbrakk> P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT; n < size LT; LT!n = OK T; P \<turnstile> T \<le> T' \<rbrakk> 
  \<Longrightarrow> P,h \<turnstile> (loc!n) :\<le> T'"
(*<*)
  apply (frule list_all2_lengthD)
  apply (drule list_all2_nthD, simp)
  apply simp
  apply (erule conf_widen, assumption+)
  done
(*>*)

lemma confTs_hext [intro?]:
  "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,h' \<turnstile> loc [:\<le>\<^sub>\<top>] LT"
  by (fast elim: list_all2_mono confT_hext)    

lemma confTs_widen [intro?, trans]:
  "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT \<Longrightarrow> P \<turnstile> LT [\<le>\<^sub>\<top>] LT' \<Longrightarrow> P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'"
  by (rule list_all2_trans, rule confT_widen)

lemma confTs_map [iff]:
  "\<And>vs. (P,h \<turnstile> vs [:\<le>\<^sub>\<top>] map OK Ts) = (P,h \<turnstile> vs [:\<le>] Ts)"
  by (induct Ts) (auto simp add: list_all2_Cons2)

lemma reg_widen_Err [iff]:
  "\<And>LT. (P \<turnstile> replicate n Err [\<le>\<^sub>\<top>] LT) = (LT = replicate n Err)"
  by (induct n) (auto simp add: list_all2_Cons1)
    
lemma confTs_Err [iff]:
  "P,h \<turnstile> replicate n v [:\<le>\<^sub>\<top>] replicate n Err"
  by (induct n) auto

  
subsection {* correct-frames *}

lemmas [simp del] = fun_upd_apply

lemma conf_fs_hext:
  "\<And>C M n T\<^sub>r. 
  \<lbrakk> conf_fs P h sh \<Phi> C M n T\<^sub>r frs; h \<unlhd> h' \<rbrakk> \<Longrightarrow> conf_fs P h' sh \<Phi> C M n T\<^sub>r frs"
(*<*)
apply (induct frs)
 apply simp
apply clarify
apply (simp (no_asm_use))
apply clarify
apply (unfold conf_f_def)
apply (simp (no_asm_use))
apply clarify
apply (fastforce elim!: confs_hext confTs_hext)
done
(*>*)

end
