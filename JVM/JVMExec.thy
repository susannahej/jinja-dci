
(*  Title:      Jinja/JVM/JVMExec.thy
    Original file by: Cornelia Pusch, Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
    Expanded to include statics and class initialization by Susannah Mansky
    2016-18, UIUC
*)

section {* Program Execution in the JVM in full small step style *}

theory JVMExec
imports JVMExecInstr
begin

abbreviation
  instrs_of :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> instr list" where
  "instrs_of P C M == fst(snd(snd(snd(snd(snd(snd(method P C M)))))))"

(* execution of single step of the initialization procedure *)
fun exec_Calling :: "[cname, cname list, jvm_prog, heap, val list, val list,
                  cname, mname, pc, frame list, sheap] \<Rightarrow> jvm_state"
where
"exec_Calling C Cs P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh =
  (case sh C of
        None \<Rightarrow> (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Calling C Cs)#frs, sh(C := Some (sblank P C, Prepared)))
      | Some (obj, iflag) \<Rightarrow>
          (case iflag of
              Done \<Rightarrow> (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Called Cs)#frs, sh)
            | Processing \<Rightarrow> (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Called Cs)#frs, sh)
            | Error \<Rightarrow> (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc,
                                   Throwing Cs (addr_of_sys_xcpt NoClassDefFoundError))#frs, sh)
            | Prepared \<Rightarrow>
                let sh' = sh(C:=Some(fst(the(sh C)), Processing));
                    D = fst(the(class P C))
                 in if C = Object
                    then (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Called (C#Cs))#frs, sh')
                    else (None, h, (stk, loc, C\<^sub>0, M\<^sub>0, pc, Calling D (C#Cs))#frs, sh')
          )
  )"

(* single step of execution without error handling *)
fun exec_step :: "[jvm_prog, heap, val list, val list,
                  cname, mname, pc, init_call_status, frame list, sheap] \<Rightarrow> jvm_state"
where
"exec_step P h stk loc C M pc (Calling C' Cs) frs sh
   = exec_Calling C' Cs P h stk loc C M pc frs sh" |
"exec_step P h stk loc C M pc (Called (C'#Cs)) frs sh
   = (None, h, create_init_frame P C'#(stk, loc, C, M, pc, Called Cs)#frs, sh)" |
"exec_step P h stk loc C M pc (Throwing (C'#Cs) a) frs sh
   = (None, h, (stk,loc,C,M,pc,Throwing Cs a)#frs, sh(C':=Some(fst(the(sh C')), Error)))" |
"exec_step P h stk loc C M pc (Throwing [] a) frs sh
   = (\<lfloor>a\<rfloor>, h, (stk,loc,C,M,pc,No_ics)#frs, sh)" |
"exec_step P h stk loc C M pc ics frs sh
   = exec_instr (instrs_of P C M ! pc) P h stk loc C M pc ics frs sh"

(* execution including error handling *)
fun exec :: "jvm_prog \<times> jvm_state \<Rightarrow> jvm_state option" \<comment> \<open>single step execution\<close> where
"exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh) =
   (let (xp', h', frs', sh') = exec_step P h stk loc C M pc ics frs sh
     in case xp' of
            None \<Rightarrow> Some (None,h',frs',sh')
          | Some x \<Rightarrow> Some (find_handler P x h ((stk,loc,C,M,pc,ics)#frs) sh)
   )"
| "exec _ = None"

\<comment> \<open>relational view\<close>
inductive_set
  exec_1 :: "jvm_prog \<Rightarrow> (jvm_state \<times> jvm_state) set"
  and exec_1' :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> jvm_state \<Rightarrow> bool" 
    ("_ \<turnstile>/ _ -jvm\<rightarrow>\<^sub>1/ _" [61,61,61] 60)
  for P :: jvm_prog
where
  "P \<turnstile> \<sigma> -jvm\<rightarrow>\<^sub>1 \<sigma>' \<equiv> (\<sigma>,\<sigma>') \<in> exec_1 P"
| exec_1I: "exec (P,\<sigma>) = Some \<sigma>' \<Longrightarrow> P \<turnstile> \<sigma> -jvm\<rightarrow>\<^sub>1 \<sigma>'"

\<comment> \<open>reflexive transitive closure:\<close>
definition exec_all :: "jvm_prog \<Rightarrow> jvm_state \<Rightarrow> jvm_state \<Rightarrow> bool"
    ("(_ \<turnstile>/ _ -jvm\<rightarrow>/ _)" [61,61,61]60) where
(* FIXME exec_all \<rightarrow> exec_star, also in Def.JVM *)
  exec_all_def1: "P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>' \<longleftrightarrow> (\<sigma>,\<sigma>') \<in> (exec_1 P)\<^sup>*"

notation (ASCII)
  exec_all  ("_ |-/ _ -jvm->/ _" [61,61,61]60)


lemma exec_1_eq:
  "exec_1 P = {(\<sigma>,\<sigma>'). exec (P,\<sigma>) = Some \<sigma>'}"
(*<*)by (auto intro: exec_1I elim: exec_1.cases)(*>*)

lemma exec_1_iff:
  "P \<turnstile> \<sigma> -jvm\<rightarrow>\<^sub>1 \<sigma>' = (exec (P,\<sigma>) = Some \<sigma>')"
(*<*)by (simp add: exec_1_eq)(*>*)

lemma exec_all_def:
  "P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>' = ((\<sigma>,\<sigma>') \<in> {(\<sigma>,\<sigma>'). exec (P,\<sigma>) = Some \<sigma>'}\<^sup>*)"
(*<*)by (simp add: exec_all_def1 exec_1_eq)(*>*)

lemma jvm_refl[iff]: "P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>"
(*<*)by(simp add: exec_all_def)(*>*)

lemma jvm_trans[trans]:
 "\<lbrakk> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'; P \<turnstile> \<sigma>' -jvm\<rightarrow> \<sigma>'' \<rbrakk> \<Longrightarrow> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>''"
(*<*)by(simp add: exec_all_def)(*>*)

lemma jvm_one_step1[trans]:
 "\<lbrakk> P \<turnstile> \<sigma> -jvm\<rightarrow>\<^sub>1 \<sigma>'; P \<turnstile> \<sigma>' -jvm\<rightarrow> \<sigma>'' \<rbrakk> \<Longrightarrow> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>''"
(*<*) by (simp add: exec_all_def1) (*>*)

lemma jvm_one_step2[trans]:
 "\<lbrakk> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'; P \<turnstile> \<sigma>' -jvm\<rightarrow>\<^sub>1 \<sigma>'' \<rbrakk> \<Longrightarrow> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>''"
(*<*) by (simp add: exec_all_def1) (*>*)

lemma exec_all_conf:
  "\<lbrakk> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'; P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'' \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<sigma>' -jvm\<rightarrow> \<sigma>'' \<or> P \<turnstile> \<sigma>'' -jvm\<rightarrow> \<sigma>'"
(*<*)by(simp add: exec_all_def single_valued_def single_valued_confluent)(*>*)

(* HERE: rename? *)
lemma exec_1_exec_all_conf:
 "\<lbrakk> exec (P, \<sigma>) = Some \<sigma>'; P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>''; \<sigma> \<noteq> \<sigma>'' \<rbrakk>
 \<Longrightarrow> P \<turnstile> \<sigma>' -jvm\<rightarrow> \<sigma>''"
 by(auto elim: converse_rtranclE simp: exec_1_eq exec_all_def)

lemma exec_all_finalD: "P \<turnstile> (x, h, [], sh) -jvm\<rightarrow> \<sigma> \<Longrightarrow> \<sigma> = (x, h, [], sh)"
(*<*)
apply(simp only: exec_all_def)
apply(erule converse_rtranclE)
 apply simp
apply simp
done
(*>*)

lemma exec_all_deterministic:
  "\<lbrakk> P \<turnstile> \<sigma> -jvm\<rightarrow> (x,h,[],sh); P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>' \<rbrakk> \<Longrightarrow> P \<turnstile> \<sigma>' -jvm\<rightarrow> (x,h,[],sh)"
(*<*)
apply(drule (1) exec_all_conf)
apply(blast dest!: exec_all_finalD)
done
(*>*)

lemma exec_Calling_prealloc_pres:
assumes "preallocated h"
  and "exec_Calling C Cs P h stk loc C\<^sub>0 M\<^sub>0 pc frs sh = (xp',h',frs',sh')"
shows "preallocated h'"
using assms
proof(cases "sh C")
  case (Some a)
  then obtain sfs i where sfsi:"a = (sfs, i)" by(cases a)
  then show ?thesis using Some assms
  proof(cases i)
    case Prepared
    then show ?thesis using sfsi Some assms by(cases "method P C clinit", auto split: if_split_asm)
  next
    case Error
    then show ?thesis using sfsi Some assms by(cases "method P C clinit", auto)
  qed(auto)
qed(auto)

lemma exec_step_prealloc_pres:
assumes pre: "preallocated h"
  and "exec_step P h stk loc C M pc ics frs sh = (xp',h',frs',sh')"
shows "preallocated h'"
proof(cases ics)
  case No_ics
  then show ?thesis using exec_instr_prealloc_pres assms by auto
next
  case Calling
  then show ?thesis using exec_Calling_prealloc_pres assms by auto
next
  case (Called Cs)
  then show ?thesis using exec_instr_prealloc_pres assms by(cases Cs, auto)
next
  case (Throwing Cs a)
  then show ?thesis using assms by(cases Cs, auto)
qed

lemma exec_prealloc_pres:
assumes pre: "preallocated h"
  and "exec (P, xp, h, frs, sh) = Some(xp',h',frs',sh')"
shows "preallocated h'"
using assms
proof(cases "\<exists>x. xp = \<lfloor>x\<rfloor> \<or> frs = []")
  case False
  then obtain f1 frs1 where frs: "frs = f1#frs1" by(cases frs, simp+)
  then obtain stk1 loc1 C1 M1 pc1 ics1 where f1: "f1 = (stk1,loc1,C1,M1,pc1,ics1)" by(cases f1)
  let ?i = "instrs_of P C1 M1 ! pc1"
  obtain xp2 h2 frs2 sh2
     where exec_step: "exec_step P h stk1 loc1 C1 M1 pc1 ics1 frs1 sh = (xp2,h2,frs2,sh2)"
    by(cases "exec_step P h stk1 loc1 C1 M1 pc1 ics1 frs1 sh")
  then show ?thesis using exec_step_prealloc_pres[OF pre exec_step] f1 frs False assms
  proof(cases xp2)
    case (Some a)
    show ?thesis
      using find_handler_prealloc_pres[OF pre, where a=a]
            exec_step_prealloc_pres[OF pre]
            exec_step f1 frs Some False assms
       by(auto split: bool.splits init_call_status.splits list.splits)
  qed(auto split: init_call_status.splits)
qed(auto)


text {*
  The start configuration of the JVM: in the start heap, we call a 
  method @{text M} of class @{text C} in program @{text P}. There is
  no @{text this} pointer of the frame as the initial method must
  be Static.
  The sheap is set to have every class pre-prepared; this decision is not necessary.
  We start with an init flag that calls for the initialization of
  the initial class.
*}
definition start_state :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> jvm_state option" where
  "start_state P C M =
 (if (\<exists>D Ts m. P \<turnstile> C sees M,Static:Ts \<rightarrow> Void = m in D)
  then let (D,sb,Ts,T,mxs,mxl\<^sub>0,b) = method P C M
       in (Some (None, start_heap P, [([], replicate mxl\<^sub>0 undefined, C, M, 0, Calling C [])], start_sheap P))
  else None
 )"

(* HERE: MOVE? *)
lemma preallocated_start_state: "start_state P C M = Some \<sigma> \<Longrightarrow> preallocated (fst(snd \<sigma>))"
using preallocated_start[of P]
 by(cases "\<exists>D Ts m. P \<turnstile> C sees M, Static :  Ts\<rightarrow>Void = m in D",
     auto simp: start_state_def)

end