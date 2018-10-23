(*  Title:      HOL/MicroJava/J/Exceptions.thy

    Author:     Gerwin Klein, Martin Strecker
    Copyright   2002 Technische Universitaet Muenchen
*)
(*
  Expanded to include more error types in support of statics and dynamic
 class initialization.
  Susannah Mansky
  2016-17, UIUC
*)

section {* Exceptions *}

theory Exceptions imports Objects begin

definition ErrorCl :: "string" where "ErrorCl = ''Error''"
definition ThrowCl :: "string" where "ThrowCl = ''Throwable''"

definition NullPointer :: cname
where
  "NullPointer \<equiv> ''NullPointer''"

definition ClassCast :: cname
where
  "ClassCast \<equiv> ''ClassCast''"

definition OutOfMemory :: cname
where
  "OutOfMemory \<equiv> ''OutOfMemory''"

definition NoClassDefFoundError :: cname
where
  "NoClassDefFoundError \<equiv> ''NoClassDefFoundError''"

definition ExceptionInInitializerError :: cname
where
  "ExceptionInInitializerError \<equiv> ''ExceptionInInitializerError''"

definition IncompatibleClassChangeError :: cname
where
  "IncompatibleClassChangeError \<equiv> ''IncompatibleClassChangeError''"

definition NoSuchFieldError :: cname
where
  "NoSuchFieldError \<equiv> ''NoSuchFieldError''"

definition NoSuchMethodError :: cname
where
  "NoSuchMethodError \<equiv> ''NoSuchMethodError''"

definition AbstractMethodError :: cname
where
  "AbstractMethodError \<equiv> ''AbstractMethodError''"

definition sys_xcpts :: "cname set"
where
  "sys_xcpts  \<equiv>  {NullPointer, ClassCast, OutOfMemory, NoClassDefFoundError,
                    ExceptionInInitializerError, IncompatibleClassChangeError, 
                    NoSuchFieldError, NoSuchMethodError, AbstractMethodError}"

definition addr_of_sys_xcpt :: "cname \<Rightarrow> addr"
where
  "addr_of_sys_xcpt s \<equiv> if s = NullPointer then 0 else
                        if s = ClassCast then 1 else
                        if s = OutOfMemory then 2 else
                        if s = NoClassDefFoundError then 3 else
                        if s = ExceptionInInitializerError then 4 else
                        if s = IncompatibleClassChangeError then 5 else
                        if s = NoSuchFieldError then 6 else
                        if s = NoSuchMethodError then 7 else
                        if s = AbstractMethodError then 8 else undefined"

(* pre-linked version *)
definition start_heap :: "'c prog \<Rightarrow> heap"
where
  "start_heap G \<equiv> Map.empty (addr_of_sys_xcpt NullPointer \<mapsto> blank G NullPointer)
                        (addr_of_sys_xcpt ClassCast \<mapsto> blank G ClassCast)
                        (addr_of_sys_xcpt OutOfMemory \<mapsto> blank G OutOfMemory)
                        (addr_of_sys_xcpt NoClassDefFoundError \<mapsto> blank G NoClassDefFoundError)
                        (addr_of_sys_xcpt ExceptionInInitializerError \<mapsto> blank G ExceptionInInitializerError)
                        (addr_of_sys_xcpt IncompatibleClassChangeError \<mapsto> blank G IncompatibleClassChangeError)
                        (addr_of_sys_xcpt NoSuchFieldError \<mapsto> blank G NoSuchFieldError)
                        (addr_of_sys_xcpt NoSuchMethodError \<mapsto> blank G NoSuchMethodError)
                        (addr_of_sys_xcpt AbstractMethodError \<mapsto> blank G AbstractMethodError)"

(* added below def to allow exception classes to be linked only when needed; paired with
 the ability in the semantics to initialize exception types when used - SM *)
definition unlinked_start_heap :: "heap"
where
  "unlinked_start_heap \<equiv> Map.empty"

(* HERE: what if we want to create an instance with an argument? *)
(*
definition exception_call :: "'c prog \<Rightarrow> cname \<Rightarrow> heap \<Rightarrow> heap" where
"exception_call P xpn h \<equiv>
 case h(addr_of_sys_xcpt xpn) of \<lfloor>x\<rfloor> \<Rightarrow> h | None \<Rightarrow> h (addr_of_sys_xcpt xpn \<mapsto> blank P xpn)"
*)


definition preallocated :: "heap \<Rightarrow> bool"
where
  "preallocated h \<equiv> \<forall>C \<in> sys_xcpts. \<exists>fs. h(addr_of_sys_xcpt C) = Some (C,fs)"

subsection "System exceptions"

lemma [simp]: "NullPointer \<in> sys_xcpts \<and> OutOfMemory \<in> sys_xcpts \<and> ClassCast \<in> sys_xcpts
   \<and> NoClassDefFoundError \<in> sys_xcpts \<and> ExceptionInInitializerError \<in> sys_xcpts
   \<and> IncompatibleClassChangeError \<in> sys_xcpts \<and> NoSuchFieldError \<in> sys_xcpts
   \<and> NoSuchMethodError \<in> sys_xcpts \<and> AbstractMethodError \<in> sys_xcpts"
(*<*)by(simp add: sys_xcpts_def)(*>*)


lemma sys_xcpts_cases [consumes 1, cases set]:
  "\<lbrakk> C \<in> sys_xcpts; P NullPointer; P OutOfMemory; P ClassCast; P NoClassDefFoundError;
  P ExceptionInInitializerError; P IncompatibleClassChangeError; P NoSuchFieldError;
  P NoSuchMethodError; P AbstractMethodError \<rbrakk> \<Longrightarrow> P C"
(*<*)by (auto simp add: sys_xcpts_def)(*>*)

lemma num_neq_aux:
 "(0::nat)\<noteq>1" "(0::nat)\<noteq>2" "(0::nat)\<noteq>3" "(0::nat)\<noteq>4" "(0::nat)\<noteq>5" "(0::nat)\<noteq>6" "(0::nat)\<noteq>7" "(0::nat)\<noteq>8"
 "(1::nat)\<noteq>2" "(1::nat)\<noteq>3" "(1::nat)\<noteq>4" "(1::nat)\<noteq>5" "(1::nat)\<noteq>6" "(1::nat)\<noteq>7" "(1::nat)\<noteq>8"
 "(2::nat)\<noteq>3" "(2::nat)\<noteq>4" "(2::nat)\<noteq>5" "(2::nat)\<noteq>6" "(2::nat)\<noteq>7" "(2::nat)\<noteq>8"
 "(3::nat)\<noteq>4" "(3::nat)\<noteq>5" "(3::nat)\<noteq>6" "(3::nat)\<noteq>7" "(3::nat)\<noteq>8"
 "(4::nat)\<noteq>5" "(4::nat)\<noteq>6" "(4::nat)\<noteq>7" "(4::nat)\<noteq>8"
 "(5::nat)\<noteq>6" "(5::nat)\<noteq>7" "(5::nat)\<noteq>8"
 "(6::nat)\<noteq>7" "(6::nat)\<noteq>8"
 "(7::nat)\<noteq>8"
 by auto

(* HERE: MAKE THIS BETTER *)
lemma start_heap_sys_xcpts:
assumes "C \<in> sys_xcpts"
shows "start_heap P (addr_of_sys_xcpt C) = Some(blank P C)"
apply(rule sys_xcpts_cases[OF assms])
apply(auto simp only: start_heap_def sys_xcpts_def fun_upd_apply
                     addr_of_sys_xcpt_def preallocated_def)
apply (smt num_neq_aux)+ (* HERE: spins a little while but finishes *)
done

subsection "@{term preallocated}"

lemma preallocated_dom [simp]: 
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> addr_of_sys_xcpt C \<in> dom h"
(*<*)by (fastforce simp:preallocated_def dom_def)(*>*)


lemma preallocatedD:
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> \<exists>fs. h(addr_of_sys_xcpt C) = Some (C, fs)"
(*<*)by(auto simp add: preallocated_def sys_xcpts_def)(*>*)


lemma preallocatedE [elim?]:
  "\<lbrakk> preallocated h;  C \<in> sys_xcpts; \<And>fs. h(addr_of_sys_xcpt C) = Some(C,fs) \<Longrightarrow> P h C\<rbrakk>
  \<Longrightarrow> P h C"
(*<*)by (fast dest: preallocatedD)(*>*)


lemma cname_of_xcp [simp]:
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> cname_of h (addr_of_sys_xcpt C) = C"
(*<*)by (auto elim: preallocatedE)(*>*)


lemma typeof_ClassCast [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt ClassCast)) = Some(Class ClassCast)" 
(*<*)by (auto elim: preallocatedE)(*>*)


lemma typeof_OutOfMemory [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt OutOfMemory)) = Some(Class OutOfMemory)" 
(*<*)by (auto elim: preallocatedE)(*>*)


lemma typeof_NullPointer [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt NullPointer)) = Some(Class NullPointer)" 
(*<*)by (auto elim: preallocatedE)(*>*)

lemma typeof_NoClassDefFoundError [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt NoClassDefFoundError)) = Some(Class NoClassDefFoundError)" 
(*<*)by (auto elim: preallocatedE)(*>*)

lemma typeof_ExceptionInInitializerError [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt ExceptionInInitializerError)) = Some(Class ExceptionInInitializerError)" 
(*<*)by (auto elim: preallocatedE)(*>*)

lemma typeof_IncompatibleClassChangeError [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt IncompatibleClassChangeError)) = Some(Class IncompatibleClassChangeError)" 
(*<*)by (auto elim: preallocatedE)(*>*)

lemma typeof_NoSuchFieldError [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt NoSuchFieldError)) = Some(Class NoSuchFieldError)" 
(*<*)by (auto elim: preallocatedE)(*>*)

lemma typeof_NoSuchMethodError [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt NoSuchMethodError)) = Some(Class NoSuchMethodError)" 
(*<*)by (auto elim: preallocatedE)(*>*)

lemma typeof_AbstractMethodError [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt AbstractMethodError)) = Some(Class AbstractMethodError)" 
(*<*)by (auto elim: preallocatedE)(*>*)

lemma preallocated_hext:
  "\<lbrakk> preallocated h; h \<unlhd> h' \<rbrakk> \<Longrightarrow> preallocated h'"
(*<*)by (simp add: preallocated_def hext_def)(*>*)

(*<*)
lemmas preallocated_upd_obj = preallocated_hext [OF _ hext_upd_obj]
lemmas preallocated_new  = preallocated_hext [OF _ hext_new]
(*>*)


(* HERE: Extremely slow to prove with any number of exceptions above 4 or 5.
 Do we need/use this? Is there a better way to prove it? *)
(* lemma preallocated_start:
  "preallocated (start_heap P)"
(*<*) apply (auto simp only: start_heap_def blank_def sys_xcpts_def fun_upd_apply
                     addr_of_sys_xcpt_def preallocated_def)(*>*)
oops (* true, but costly to prove *) *)
lemma preallocated_start:
  "preallocated (start_heap P)"
 by(auto simp: start_heap_sys_xcpts blank_def preallocated_def)

end
