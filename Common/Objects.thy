(*  Title:      HOL/MicroJava/J/State.thy

    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)
(*
  Expanded to include statics
  Susannah Mansky
  2016-17, UIUC
*)

section {* Objects and the Heap *}

theory Objects imports TypeRel Value Subcls begin

subsection{* Objects *}

type_synonym
  fields = "vname \<times> cname \<rightharpoonup> val"  \<comment> \<open>field name, defining class, value\<close>
type_synonym
  obj = "cname \<times> fields"    \<comment> \<open>class instance with class name and fields\<close>
type_synonym
  sfields = "vname \<rightharpoonup> val"  \<comment> \<open>field name to value\<close>

definition obj_ty  :: "obj \<Rightarrow> ty"
where
  "obj_ty obj  \<equiv>  Class (fst obj)"

(* initializes a given list of fields *)
definition init_fields :: "((vname \<times> cname) \<times> staticb \<times> ty) list \<Rightarrow> fields"
where
  "init_fields FDTs  \<equiv>  (map_of \<circ> map (\<lambda>((F,D),b,T). ((F,D),default_val T))) FDTs"

definition init_sfields :: "((vname \<times> cname) \<times> staticb \<times> ty) list \<Rightarrow> sfields"
where
  "init_sfields FDTs  \<equiv>  (map_of \<circ> map (\<lambda>((F,D),b,T). (F,default_val T))) FDTs"
  
  \<comment> \<open>a new, blank object with default values for instance fields:\<close>
definition blank :: "'m prog \<Rightarrow> cname \<Rightarrow> obj"
where
  "blank P C \<equiv>  (C,init_fields (ifields P C))"

  \<comment> \<open>a new, blank object with default values for static fields:\<close>
definition sblank :: "'m prog \<Rightarrow> cname \<Rightarrow> sfields"
where
  "sblank P C \<equiv> init_sfields (isfields P C)"

lemma [simp]: "obj_ty (C,fs) = Class C"
(*<*)by (simp add: obj_ty_def)(*>*)

(* replaced all vname, cname in below with `char list' and \<rightharpoonup> with returned option
  so that pretty printing works *)
translations
  (type) "fields" <= (type) "char list \<times> char list \<Rightarrow> val option"
  (type) "obj" <= (type) "char list \<times> fields"
  (type) "sfields" <= (type) "char list \<Rightarrow> val option"

subsection{* Heap *}

type_synonym heap  = "addr \<rightharpoonup> obj"

(* replaced addr with nat and \<rightharpoonup> with returned option so that pretty printing works *)
translations
 (type) "heap" <= (type) "nat \<Rightarrow> obj option"

abbreviation
  cname_of :: "heap \<Rightarrow> addr \<Rightarrow> cname" where
  "cname_of hp a == fst (the (hp a))"

definition new_Addr  :: "heap \<Rightarrow> addr option"
where
  "new_Addr h  \<equiv>  if \<exists>a. h a = None then Some(LEAST a. h a = None) else None"

definition cast_ok :: "'m prog \<Rightarrow> cname \<Rightarrow> heap \<Rightarrow> val \<Rightarrow> bool"
where
  "cast_ok P C h v  \<equiv>  v = Null \<or> P \<turnstile> cname_of h (the_Addr v) \<preceq>\<^sup>* C"

(* HERE: might want to move this definition -SM *)
definition checkcast_class_collect :: "'m prog \<Rightarrow> cname \<Rightarrow> heap \<Rightarrow> val \<Rightarrow> cname set" where
"checkcast_class_collect P C h v \<equiv> if v = Null then {}
                                   (* else if P \<turnstile> cname_of h (the_Addr v) \<preceq>\<^sup>* C
                                        then classes_between P (cname_of h (the_Addr v)) C *)
                                        else classes_above P (cname_of h (the_Addr v))"

definition hext :: "heap \<Rightarrow> heap \<Rightarrow> bool" ("_ \<unlhd> _" [51,51] 50)
where
  "h \<unlhd> h'  \<equiv>  \<forall>a C fs. h a = Some(C,fs) \<longrightarrow> (\<exists>fs'. h' a = Some(C,fs'))"

primrec typeof_h :: "heap \<Rightarrow> val \<Rightarrow> ty option"  ("typeof\<^bsub>_\<^esub>")
where
  "typeof\<^bsub>h\<^esub>  Unit    = Some Void"
| "typeof\<^bsub>h\<^esub>  Null    = Some NT"
| "typeof\<^bsub>h\<^esub> (Bool b) = Some Boolean"
| "typeof\<^bsub>h\<^esub> (Intg i) = Some Integer"
| "typeof\<^bsub>h\<^esub> (Addr a) = (case h a of None \<Rightarrow> None | Some(C,fs) \<Rightarrow> Some(Class C))"

lemma new_Addr_SomeD:
  "new_Addr h = Some a \<Longrightarrow> h a = None"
 (*<*)by(fastforce simp add:new_Addr_def split:if_splits intro:LeastI)(*>*)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some Boolean) = (\<exists>b. v = Bool b)"
 (*<*)by(induct v) auto(*>*)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some Integer) = (\<exists>i. v = Intg i)"
(*<*)by(cases v) auto(*>*)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some NT) = (v = Null)"
 (*<*)by(cases v) auto(*>*)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some(Class C)) = (\<exists>a fs. v = Addr a \<and> h a = Some(C,fs))"
 (*<*)by(cases v) auto(*>*)

lemma [simp]: "h a = Some(C,fs) \<Longrightarrow> typeof\<^bsub>(h(a\<mapsto>(C,fs')))\<^esub> v = typeof\<^bsub>h\<^esub> v"
 (*<*)by(induct v) (auto simp:fun_upd_apply)(*>*)

text{* For literal values the first parameter of @{term typeof} can be
set to @{term empty} because they do not contain addresses: *}

abbreviation
  typeof :: "val \<Rightarrow> ty option" where
  "typeof v == typeof_h Map.empty v"

lemma typeof_lit_typeof:
  "typeof v = Some T \<Longrightarrow> typeof\<^bsub>h\<^esub> v = Some T"
 (*<*)by(cases v) auto(*>*)

lemma typeof_lit_is_type: 
  "typeof v = Some T \<Longrightarrow> is_type P T"
 (*<*)by (induct v) (auto simp:is_type_def)(*>*)


subsection {* Heap extension @{text"\<unlhd>"} *}

lemma hextI: "\<forall>a C fs. h a = Some(C,fs) \<longrightarrow> (\<exists>fs'. h' a = Some(C,fs')) \<Longrightarrow> h \<unlhd> h'"
(*<*)
apply (unfold hext_def)
apply auto
done
(*>*)

lemma hext_objD: "\<lbrakk> h \<unlhd> h'; h a = Some(C,fs) \<rbrakk> \<Longrightarrow> \<exists>fs'. h' a = Some(C,fs')"
(*<*)
apply (unfold hext_def)
apply (force)
done
(*>*)

lemma hext_refl [iff]: "h \<unlhd> h"
(*<*)
apply (rule hextI)
apply (fast)
done
(*>*)

lemma hext_new [simp]: "h a = None \<Longrightarrow> h \<unlhd> h(a\<mapsto>x)"
(*<*)
apply (rule hextI)
apply (auto simp:fun_upd_apply)
done
(*>*)

lemma hext_trans: "\<lbrakk> h \<unlhd> h'; h' \<unlhd> h'' \<rbrakk> \<Longrightarrow> h \<unlhd> h''"
(*<*)
apply (rule hextI)
apply (fast dest: hext_objD)
done
(*>*)

lemma hext_upd_obj: "h a = Some (C,fs) \<Longrightarrow> h \<unlhd> h(a\<mapsto>(C,fs'))"
(*<*)
apply (rule hextI)
apply (auto simp:fun_upd_apply)
done
(*>*)

lemma hext_typeof_mono: "\<lbrakk> h \<unlhd> h'; typeof\<^bsub>h\<^esub> v = Some T \<rbrakk> \<Longrightarrow> typeof\<^bsub>h'\<^esub> v = Some T"
(*<*)
apply(cases v)
    apply simp
   apply simp
  apply simp
 apply simp
apply(fastforce simp:hext_def)
done
(*>*)

text {* Code generator setup for @{term "new_Addr"} *}

definition gen_new_Addr :: "heap \<Rightarrow> addr \<Rightarrow> addr option"
where "gen_new_Addr h n \<equiv> if \<exists>a. a \<ge> n \<and> h a = None then Some(LEAST a. a \<ge> n \<and> h a = None) else None"

lemma new_Addr_code_code [code]:
  "new_Addr h = gen_new_Addr h 0"
by(simp add: new_Addr_def gen_new_Addr_def split del: if_split cong: if_cong)

lemma gen_new_Addr_code [code]:
  "gen_new_Addr h n = (if h n = None then Some n else gen_new_Addr h (Suc n))"
apply(simp add: gen_new_Addr_def)
apply(rule impI)
apply(rule conjI)
 apply safe[1]
  apply(fastforce intro: Least_equality)
 apply(rule arg_cong[where f=Least])
 apply(rule ext)
 apply(case_tac "n = ac")
  apply simp
 apply(auto)[1]
apply clarify
apply(subgoal_tac "a = n")
 apply simp
 apply(rule Least_equality)
 apply auto[2]
apply(rule ccontr)
apply(erule_tac x="a" in allE)
apply simp
done


subsection{* Static field information function *}

datatype init_state = Done | Processing | Prepared | Error
	\<comment> \<open>Done = initialized\<close>
	\<comment> \<open>Processing = currently being initialized\<close>
	\<comment> \<open>Prepared = uninitialized and not currently being initialized\<close>
	\<comment> \<open>Error = previous initialization attempt resulted in erroneous state\<close>

inductive iprog :: "init_state \<Rightarrow> init_state \<Rightarrow> bool" ("_ \<le>\<^sub>i _" [51,51] 50)
where
  [simp]: "Prepared \<le>\<^sub>i i"
| [simp]: "Processing \<le>\<^sub>i Done"
| [simp]: "Processing \<le>\<^sub>i Error"
| [simp]: "i \<le>\<^sub>i i"

lemma iprog_Done[simp]: "(Done \<le>\<^sub>i i) = (i = Done)"
 by(simp only: iprog.simps, simp)

lemma iprog_Error[simp]: "(Error \<le>\<^sub>i i) = (i = Error)"
 by(simp only: iprog.simps, simp)

lemma iprog_Processing[simp]: "(Processing \<le>\<^sub>i i) = (i = Done \<or> i = Error \<or> i = Processing)"
 by(simp only: iprog.simps, simp)

lemma iprog_trans: "\<lbrakk> i \<le>\<^sub>i i'; i' \<le>\<^sub>i i'' \<rbrakk> \<Longrightarrow> i \<le>\<^sub>i i''"
apply(case_tac i, simp_all)
apply(case_tac i', simp_all)
done

type_synonym
  sheap = "cname \<rightharpoonup> sfields \<times> init_state"
  \<comment> \<open>For storing information about static field values and initialization status for classes\<close>

translations
 (type) "sheap" <= (type) "char list \<Rightarrow> (sfields \<times> init_state) option"

definition shext :: "sheap \<Rightarrow> sheap \<Rightarrow> bool" ("_ \<unlhd>\<^sub>s _" [51,51] 50)
where
  "sh \<unlhd>\<^sub>s sh'  \<equiv>  \<forall>C sfs i. sh C = Some(sfs,i) \<longrightarrow> (\<exists>sfs' i'. sh' C = Some(sfs',i') \<and> i \<le>\<^sub>i i')"

subsection {* SHeap extension @{text"\<unlhd>\<^sub>s"} *}

lemma shextI: "\<forall>C sfs i. sh C = Some(sfs,i) \<longrightarrow> (\<exists>sfs' i'. sh' C = Some(sfs',i') \<and> i \<le>\<^sub>i i') \<Longrightarrow> sh \<unlhd>\<^sub>s sh'"
(*<*)
apply (unfold shext_def)
apply auto
done
(*>*)

lemma shext_objD: "\<lbrakk> sh \<unlhd>\<^sub>s sh'; sh C = Some(sfs,i) \<rbrakk> \<Longrightarrow> \<exists>sfs' i'. sh' C = Some(sfs', i') \<and> i \<le>\<^sub>i i'"
(*<*)
apply (unfold shext_def)
apply (force)
done
(*>*)

lemma shext_refl [iff]: "sh \<unlhd>\<^sub>s sh"
(*<*)
apply (rule shextI)
apply auto
done
(*>*)

lemma shext_new [simp]: "sh C = None \<Longrightarrow> sh \<unlhd>\<^sub>s sh(C\<mapsto>x)"
(*<*)
apply (rule shextI)
apply (auto simp:fun_upd_apply)
done
(*>*)

lemma shext_trans: "\<lbrakk> sh \<unlhd>\<^sub>s sh'; sh' \<unlhd>\<^sub>s sh'' \<rbrakk> \<Longrightarrow> sh \<unlhd>\<^sub>s sh''"
(*<*)
apply (rule shextI)
apply (fast dest: iprog_trans shext_objD)
done
(*>*)

lemma shext_upd_obj: "\<lbrakk> sh C = Some (sfs,i); i \<le>\<^sub>i i' \<rbrakk> \<Longrightarrow> sh \<unlhd>\<^sub>s sh(C\<mapsto>(sfs',i'))"
(*<*)
apply (rule shextI)
apply (auto simp:fun_upd_apply)
done
(*>*)

end