(*  Title:      JinjaDCI/Common/WellForm.thy

    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   2003 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory J/WellForm.thy by Tobias Nipkow
*)

section \<open> Generic Well-formedness of programs \<close>

theory WellForm imports TypeRel SystemClasses begin

text \<open>\noindent This theory defines global well-formedness conditions
for programs but does not look inside method bodies.  Hence it works
for both Jinja and JVM programs. Well-typing of expressions is defined
elsewhere (in theory @{text WellType}).

Because Jinja does not have method overloading, its policy for method
overriding is the classical one: \emph{covariant in the result type
but contravariant in the argument types.} This means the result type
of the overriding method becomes more specific, the argument types
become more general.
\<close>

type_synonym 'm wf_mdecl_test = "'m prog \<Rightarrow> cname \<Rightarrow> 'm mdecl \<Rightarrow> bool"

definition wf_fdecl :: "'m prog \<Rightarrow> fdecl \<Rightarrow> bool"
where
  "wf_fdecl P \<equiv> \<lambda>(F,b,T). is_type P T"

definition wf_mdecl :: "'m wf_mdecl_test \<Rightarrow> 'm wf_mdecl_test"
where
  "wf_mdecl wf_md P C \<equiv> \<lambda>(M,b,Ts,T,m).
  (\<forall>T\<in>set Ts. is_type P T) \<and> is_type P T \<and> wf_md P C (M,b,Ts,T,m)"

definition wf_clinit :: "'m mdecl list \<Rightarrow> bool" where
"wf_clinit ms = (\<exists>m. (clinit,Static,[],Void,m)\<in>set ms)"

definition wf_cdecl :: "'m wf_mdecl_test \<Rightarrow> 'm prog \<Rightarrow> 'm cdecl \<Rightarrow> bool"
where
  "wf_cdecl wf_md P  \<equiv>  \<lambda>(C,(D,fs,ms)).
  (\<forall>f\<in>set fs. wf_fdecl P f) \<and>  distinct_fst fs \<and>
  (\<forall>m\<in>set ms. wf_mdecl wf_md P C m) \<and>  distinct_fst ms \<and>
  (C \<noteq> Object \<longrightarrow>
   is_class P D \<and> \<not> P \<turnstile> D \<preceq>\<^sup>* C \<and>
   (\<forall>(M,b,Ts,T,m)\<in>set ms.
      \<forall>D' b' Ts' T' m'. P \<turnstile> D sees M,b':Ts' \<rightarrow> T' = m' in D' \<longrightarrow>
                       b = b' \<and> P \<turnstile> Ts' [\<le>] Ts \<and> P \<turnstile> T \<le> T')) \<and>
  wf_clinit ms"

definition wf_syscls :: "'m prog \<Rightarrow> bool"
where
  "wf_syscls P  \<equiv>  {Object} \<union> sys_xcpts \<subseteq> set(map fst P)"

definition wf_prog :: "'m wf_mdecl_test \<Rightarrow> 'm prog \<Rightarrow> bool"
where
  "wf_prog wf_md P  \<equiv>  wf_syscls P \<and> (\<forall>c \<in> set P. wf_cdecl wf_md P c) \<and> distinct_fst P"


subsection\<open> Well-formedness lemmas \<close>

lemma class_wf: 
  "\<lbrakk>class P C = Some c; wf_prog wf_md P\<rbrakk> \<Longrightarrow> wf_cdecl wf_md P (C,c)"
(*<*)
apply (unfold wf_prog_def class_def)
apply (fast dest: map_of_SomeD)
done
(*>*)


lemma class_Object [simp]: 
  "wf_prog wf_md P \<Longrightarrow> \<exists>C fs ms. class P Object = Some (C,fs,ms)"
(*<*)
apply (unfold wf_prog_def wf_syscls_def class_def)
apply (auto simp: map_of_SomeI)
done
(*>*)


lemma is_class_Object [simp]:
  "wf_prog wf_md P \<Longrightarrow> is_class P Object"
(*<*)by (simp add: is_class_def)(*>*)

lemma is_class_supclass:
assumes wf: "wf_prog wf_md P" and sub: "P \<turnstile> C \<preceq>\<^sup>* D"
shows "is_class P C \<Longrightarrow> is_class P D"
using sub apply(induct)
 apply assumption
apply(auto simp:wf_cdecl_def is_class_def
           dest!:class_wf[OF _ wf] subcls1D)
done

lemma is_class_xcpt:
  "\<lbrakk> C \<in> sys_xcpts; wf_prog wf_md P \<rbrakk> \<Longrightarrow> is_class P C"
(*<*)
  apply (simp add: wf_prog_def wf_syscls_def is_class_def class_def)
  apply (fastforce intro!: map_of_SomeI)
  done
(*>*)


lemma subcls1_wfD:
  "\<lbrakk> P \<turnstile> C \<prec>\<^sup>1 D; wf_prog wf_md P \<rbrakk> \<Longrightarrow> D \<noteq> C \<and> (D,C) \<notin> (subcls1 P)\<^sup>+"
(*<*)
apply( frule r_into_trancl)
apply( drule subcls1D)
apply(clarify)
apply( drule (1) class_wf)
apply( unfold wf_cdecl_def)
apply(force simp add: reflcl_trancl [THEN sym] simp del: reflcl_trancl)
done
(*>*)


lemma wf_cdecl_supD: 
  "\<lbrakk>wf_cdecl wf_md P (C,D,r); C \<noteq> Object\<rbrakk> \<Longrightarrow> is_class P D"
(*<*)by (auto simp: wf_cdecl_def)(*>*)


lemma subcls_asym:
  "\<lbrakk> wf_prog wf_md P; (C,D) \<in> (subcls1 P)\<^sup>+ \<rbrakk> \<Longrightarrow> (D,C) \<notin> (subcls1 P)\<^sup>+"
(*<*)
apply(erule tranclE)
apply(fast dest!: subcls1_wfD )
apply(fast dest!: subcls1_wfD intro: trancl_trans)
done
(*>*)


lemma subcls_irrefl:
  "\<lbrakk> wf_prog wf_md P; (C,D) \<in> (subcls1 P)\<^sup>+ \<rbrakk> \<Longrightarrow> C \<noteq> D"
(*<*)
apply (erule trancl_trans_induct)
apply  (auto dest: subcls1_wfD subcls_asym)
done
(*>*)


lemma acyclic_subcls1:
  "wf_prog wf_md P \<Longrightarrow> acyclic (subcls1 P)"
(*<*)
apply (unfold acyclic_def)
apply (fast dest: subcls_irrefl)
done
(*>*)


lemma wf_subcls1:
  "wf_prog wf_md P \<Longrightarrow> wf ((subcls1 P)\<inverse>)"
(*<*)
apply (rule finite_acyclic_wf)
apply ( subst finite_converse)
apply ( rule finite_subcls1)
apply (subst acyclic_converse)
apply (erule acyclic_subcls1)
done
(*>*)


lemma single_valued_subcls1:
  "wf_prog wf_md G \<Longrightarrow> single_valued (subcls1 G)"
(*<*)
by(auto simp:wf_prog_def distinct_fst_def single_valued_def dest!:subcls1D)
(*>*)


lemma subcls_induct: 
  "\<lbrakk> wf_prog wf_md P; \<And>C. \<forall>D. (C,D) \<in> (subcls1 P)\<^sup>+ \<longrightarrow> Q D \<Longrightarrow> Q C \<rbrakk> \<Longrightarrow> Q C"
(*<*)
  (is "?A \<Longrightarrow> PROP ?P \<Longrightarrow> _")
proof -
  assume p: "PROP ?P"
  assume ?A thus ?thesis apply -
apply(drule wf_subcls1)
apply(drule wf_trancl)
apply(simp only: trancl_converse)
apply(erule_tac a = C in wf_induct)
apply(rule p)
apply(auto)
done
qed
(*>*)


lemma subcls1_induct_aux:
  "\<lbrakk> is_class P C; wf_prog wf_md P; Q Object;
    \<And>C D fs ms.
    \<lbrakk> C \<noteq> Object; is_class P C; class P C = Some (D,fs,ms) \<and>
      wf_cdecl wf_md P (C,D,fs,ms) \<and> P \<turnstile> C \<prec>\<^sup>1 D \<and> is_class P D \<and> Q D\<rbrakk> \<Longrightarrow> Q C \<rbrakk>
  \<Longrightarrow> Q C"
(*<*)
  (is "?A \<Longrightarrow> ?B \<Longrightarrow> ?C \<Longrightarrow> PROP ?P \<Longrightarrow> _")
proof -
  assume p: "PROP ?P"
  assume ?A ?B ?C thus ?thesis apply -
apply(unfold is_class_def)
apply( rule impE)
prefer 2
apply(   assumption)
prefer 2
apply(  assumption)
apply( erule thin_rl)
apply( rule subcls_induct)
apply(  assumption)
apply( rule impI)
apply( case_tac "C = Object")
apply(  fast)
apply safe
apply( frule (1) class_wf)
apply( frule (1) wf_cdecl_supD)

apply( subgoal_tac "P \<turnstile> C \<prec>\<^sup>1 a")
apply( erule_tac [2] subcls1I)
apply(  rule p)
apply (unfold is_class_def)
apply auto
done
qed
(*>*)

(* FIXME can't we prove this one directly?? *)
lemma subcls1_induct [consumes 2, case_names Object Subcls]:
  "\<lbrakk> wf_prog wf_md P; is_class P C; Q Object;
    \<And>C D. \<lbrakk>C \<noteq> Object; P \<turnstile> C \<prec>\<^sup>1 D; is_class P D; Q D\<rbrakk> \<Longrightarrow> Q C \<rbrakk>
  \<Longrightarrow> Q C"
(*<*)
  apply (erule subcls1_induct_aux, assumption, assumption)
  apply blast
  done
(*>*)


lemma subcls_C_Object:
  "\<lbrakk> is_class P C; wf_prog wf_md P \<rbrakk> \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* Object"
(*<*)
apply(erule (1) subcls1_induct)
 apply( fast)
apply(erule (1) converse_rtrancl_into_rtrancl)
done
(*>*)


lemma is_type_pTs:
assumes "wf_prog wf_md P" and "(C,S,fs,ms) \<in> set P" and "(M,b,Ts,T,m) \<in> set ms"
shows "set Ts \<subseteq> types P"
(*<*)
proof
  from assms have "wf_mdecl wf_md P C (M,b,Ts,T,m)" 
    by (unfold wf_prog_def wf_cdecl_def) auto
  hence "\<forall>t \<in> set Ts. is_type P t" by (unfold wf_mdecl_def) auto
  moreover fix t assume "t \<in> set Ts"
  ultimately have "is_type P t" by blast
  thus "t \<in> types P" ..
qed
(*>*)

lemma wf_supercls_distinct_app:
assumes wf:"wf_prog wf_md P"
  and nObj: "C \<noteq> Object" and cls: "class P C = \<lfloor>(D, fs, ms)\<rfloor>"
  and super: "supercls_lst P (C#Cs)" and dist: "distinct (C#Cs)"
shows "distinct (D#C#Cs)"
proof -
  have "\<not> P \<turnstile> D \<preceq>\<^sup>* C" using subcls1_wfD[OF subcls1I[OF cls nObj] wf]
    by (simp add: rtrancl_eq_or_trancl)
  then show ?thesis using assms by auto
qed


subsection\<open> Well-formedness and method lookup \<close>

lemma sees_wf_mdecl:
  "\<lbrakk> wf_prog wf_md P; P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D \<rbrakk> \<Longrightarrow> wf_mdecl wf_md P D (M,b,Ts,T,m)"
(*<*)
apply (case_tac b)
 apply simp
 apply(drule visible_method_exists)
 apply(fastforce simp:wf_cdecl_def dest!:class_wf dest:map_of_SomeD)
apply simp
apply(drule visible_method_exists)
apply(fastforce simp:wf_cdecl_def dest!:class_wf dest:map_of_SomeD)
done
(*>*)

lemma sees_method_mono [rule_format (no_asm)]: 
  "\<lbrakk> P \<turnstile> C' \<preceq>\<^sup>* C; wf_prog wf_md P \<rbrakk> \<Longrightarrow>
  \<forall>D b Ts T m. P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D \<longrightarrow>
     (\<exists>D' Ts' T' m'. P \<turnstile> C' sees M,b:Ts'\<rightarrow>T' = m' in D' \<and> P \<turnstile> Ts [\<le>] Ts' \<and> P \<turnstile> T' \<le> T)"
(*<*)
apply( drule rtranclD)
apply( erule disjE)
apply(  fastforce)
apply( erule conjE)
apply( erule trancl_trans_induct)
prefer 2
apply(  clarify)
apply(  drule spec, drule spec, drule spec, drule spec, drule spec, erule (1) impE)
apply clarify
apply(  fast elim: widen_trans widens_trans)
apply( clarify)
apply( drule subcls1D)
apply( clarify)
apply(clarsimp simp:Method_def)
apply(frule (2) sees_methods_rec)
apply(rule refl)
apply(case_tac "map_of ms M")
apply(rule_tac x = D in exI)
apply(rule_tac x = Ts in exI)
apply(rule_tac x = T in exI)
apply simp
apply(rule_tac x = m in exI)
apply(fastforce simp add:map_add_def split:option.split)
apply clarsimp
apply(rename_tac Ts' T' m')
apply( drule (1) class_wf)
apply( unfold wf_cdecl_def Method_def)
apply( frule map_of_SomeD)
apply auto
apply(drule (1) bspec, simp)
apply(erule_tac x=D in allE, erule_tac x=b in allE, erule_tac x=Ts in allE, erule_tac x=T in allE)
apply(fastforce simp:map_add_def split:option.split)
done
(*>*)


lemma sees_method_mono2:
  "\<lbrakk> P \<turnstile> C' \<preceq>\<^sup>* C; wf_prog wf_md P;
     P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D; P \<turnstile> C' sees M,b':Ts'\<rightarrow>T' = m' in D' \<rbrakk>
  \<Longrightarrow> b = b' \<and> P \<turnstile> Ts [\<le>] Ts' \<and> P \<turnstile> T' \<le> T"
(*<*)by(blast dest:sees_method_mono sees_method_fun)(*>*)

lemma mdecls_visible:
assumes wf: "wf_prog wf_md P" and "class": "is_class P C"
shows "\<And>D fs ms. class P C = Some(D,fs,ms)
         \<Longrightarrow> \<exists>Mm. P \<turnstile> C sees_methods Mm \<and> (\<forall>(M,b,Ts,T,m) \<in> set ms. Mm M = Some((b,Ts,T,m),C))"
(*<*)
using wf "class"
proof (induct rule:subcls1_induct)
  case Object
  with wf have dfst:"distinct_fst ms"
    by (unfold class_def wf_prog_def wf_cdecl_def) (fastforce dest:map_of_SomeD)
  with dfst have "distinct_fst ms"
    by(blast dest: distinct_fst_appendD)
  with Object show ?case by(fastforce intro!: sees_methods_Object map_of_SomeI)
next
  case Subcls
  with wf have dfst:"distinct_fst ms"
    by (unfold class_def wf_prog_def wf_cdecl_def) (fastforce dest:map_of_SomeD)
  with dfst have "distinct_fst ms"
    by(blast dest: distinct_fst_appendD)
  with Subcls show ?case
    by(fastforce elim:sees_methods_rec dest:subcls1D map_of_SomeI
                simp:is_class_def)
qed
(*>*)

lemma mdecl_visible:
assumes wf: "wf_prog wf_md P" and C: "(C,S,fs,ms) \<in> set P" and  m: "(M,b,Ts,T,m) \<in> set ms"
shows "P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in C"
(*<*)
proof -
  from wf C have "class": "class P C = Some (S,fs,ms)"
    by (auto simp add: wf_prog_def class_def is_class_def intro: map_of_SomeI)
  from "class" have "is_class P C" by(auto simp:is_class_def)                   
  with assms "class" show ?thesis
    by(bestsimp simp:Method_def dest:mdecls_visible)
qed
(*>*)


lemma Call_lemma:
  "\<lbrakk> P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D; P \<turnstile> C' \<preceq>\<^sup>* C; wf_prog wf_md P \<rbrakk>
  \<Longrightarrow> \<exists>D' Ts' T' m'.
       P \<turnstile> C' sees M,b:Ts'\<rightarrow>T' = m' in D' \<and> P \<turnstile> Ts [\<le>] Ts' \<and> P \<turnstile> T' \<le> T \<and> P \<turnstile> C' \<preceq>\<^sup>* D'
       \<and> is_type P T' \<and> (\<forall>T\<in>set Ts'. is_type P T) \<and> wf_md P D' (M,b,Ts',T',m')"
(*<*)
apply(frule (2) sees_method_mono)
apply(fastforce intro:sees_method_decl_above dest:sees_wf_mdecl
               simp: wf_mdecl_def)
done
(*>*)


lemma wf_prog_lift:
  assumes wf: "wf_prog (\<lambda>P C bd. A P C bd) P"
  and rule:
  "\<And>wf_md C M b Ts C T m bd.
   wf_prog wf_md P \<Longrightarrow>
   P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in C \<Longrightarrow>
   set Ts \<subseteq>  types P \<Longrightarrow>
   bd = (M,b,Ts,T,m) \<Longrightarrow>
   A P C bd \<Longrightarrow>
   B P C bd"
  shows "wf_prog (\<lambda>P C bd. B P C bd) P"
(*<*)
proof -
  from wf show ?thesis
    apply (unfold wf_prog_def wf_cdecl_def)
    apply clarsimp
    apply (drule bspec, assumption)
    apply (unfold wf_mdecl_def)
    apply clarsimp
    apply (drule bspec, assumption)
    apply clarsimp
    apply (frule mdecl_visible [OF wf], assumption+)
    apply (frule is_type_pTs [OF wf], assumption+)
    apply (drule rule [OF wf], assumption+)
    apply auto
    done
qed
(*>*)

lemma wf_sees_clinit:
assumes wf:"wf_prog wf_md P" and ex: "class P C = Some a"
shows "\<exists>m. P \<turnstile> C sees clinit,Static:[] \<rightarrow> Void = m in C"
proof -
  from ex obtain D fs ms where "a = (D,fs,ms)" by(cases a)
  then have sP: "(C, D, fs, ms) \<in> set P" using ex map_of_SomeD[of P C a] by(simp add: class_def)
  then have "wf_clinit ms" using assms by(unfold wf_prog_def wf_cdecl_def, auto)
  then obtain m where sm: "(clinit, Static, [], Void, m) \<in> set ms" by (meson wf_clinit_def)
  then have "P \<turnstile> C sees clinit,Static:[] \<rightarrow> Void = m in C"
    using mdecl_visible[OF wf sP sm] by simp
  then show ?thesis by(rule exI)
qed
(*>*)

lemma wf_sees_clinit1:
assumes wf:"wf_prog wf_md P" and ex: "class P C = Some a"
and "P \<turnstile> C sees clinit,b:Ts \<rightarrow> T = m in D"
shows "b = Static \<and> Ts = [] \<and> T = Void \<and> D = C"
proof -
  obtain m' where sees: "P \<turnstile> C sees clinit,Static:[] \<rightarrow> Void = m' in C"
    using wf_sees_clinit[OF wf ex] by clarify
  then show ?thesis using sees wf by (meson assms(3) sees_method_fun)
qed

lemma wf_NonStatic_nclinit:
assumes wf: "wf_prog wf_md P" and meth: "P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T=(mxs,mxl,ins,xt) in D"
shows "M \<noteq> clinit"
proof -
  from sees_method_is_class[OF meth] obtain a where cls: "class P C = Some a"
    by(clarsimp simp: is_class_def)
  with wf wf_sees_clinit[OF wf cls]
   obtain m where "P \<turnstile> C sees clinit,Static:[]\<rightarrow>Void=m in C" by clarsimp
  with meth show ?thesis by(auto dest: sees_method_fun)
qed

subsection\<open> Well-formedness and field lookup \<close>

lemma wf_Fields_Ex:
  "\<lbrakk> wf_prog wf_md P; is_class P C \<rbrakk> \<Longrightarrow> \<exists>FDTs. P \<turnstile> C has_fields FDTs"
(*<*)
apply(frule class_Object)
apply(erule (1) subcls1_induct)
 apply(blast intro:has_fields_Object)
apply(blast intro:has_fields_rec dest:subcls1D)
done
(*>*)


lemma has_fields_types:
  "\<lbrakk> P \<turnstile> C has_fields FDTs; (FD,b,T) \<in> set FDTs; wf_prog wf_md P \<rbrakk> \<Longrightarrow> is_type P T"
(*<*)
apply(induct rule:Fields.induct)
 apply(fastforce dest!: class_wf simp: wf_cdecl_def wf_fdecl_def)
apply(fastforce dest!: class_wf simp: wf_cdecl_def wf_fdecl_def)
done
(*>*)

lemma sees_field_is_type:
  "\<lbrakk> P \<turnstile> C sees F,b:T in D; wf_prog wf_md P \<rbrakk> \<Longrightarrow> is_type P T"
(*<*)
  by (meson has_field_def has_fields_types has_visible_field map_of_SomeD)
(*>*)


lemma wf_syscls:
  "set SystemClasses \<subseteq> set P \<Longrightarrow> wf_syscls P"
(*<*)
apply (simp add: image_def SystemClasses_def wf_syscls_def sys_xcpts_def
                 ObjectC_def NullPointerC_def ClassCastC_def OutOfMemoryC_def
                 NoClassDefFoundC_def
                 IncompatibleClassChangeC_def NoSuchFieldC_def NoSuchMethodC_def)
apply force
done
(*>*)


subsection\<open> Well-formedness and subclassing \<close>

lemma wf_subcls_nCls:
assumes wf: "wf_prog wf_md P" and ns: "\<not> is_class P C"
shows "\<lbrakk> P \<turnstile> D \<preceq>\<^sup>* D'; D \<noteq> C \<rbrakk> \<Longrightarrow> D' \<noteq> C"
proof(induct rule: rtrancl.induct)
  case (rtrancl_into_rtrancl a b c)
  with ns show ?case by(clarsimp dest!: subcls1D wf_cdecl_supD[OF class_wf[OF _ wf]])
qed(simp)

lemma wf_subcls_nCls':
assumes wf: "wf_prog wf_md P" and ns: "\<not>is_class P C\<^sub>0"
shows "\<And>cd D'. cd \<in> set P \<Longrightarrow> \<not>P \<turnstile> fst cd \<preceq>\<^sup>* C\<^sub>0"
proof -
  fix cd D' assume cd: "cd \<in> set P"
  then have cls: "is_class P (fst cd)" using class_exists_equiv is_class_def by blast
  with wf_subcls_nCls[OF wf ns] ns show "\<not>P \<turnstile> fst cd \<preceq>\<^sup>* C\<^sub>0" by(cases "fst cd = D'", auto)
qed

lemma wf_nclass_nsub:
 "\<lbrakk> wf_prog wf_md P; is_class P C; \<not>is_class P C' \<rbrakk> \<Longrightarrow> \<not>P \<turnstile> C \<preceq>\<^sup>* C'"
 by(rule notI, auto dest: wf_subcls_nCls[where C=C' and D=C])

lemma wf_sys_xcpt_nsub_Start:
assumes wf: "wf_prog wf_md P" and ns: "\<not>is_class P Start" and sx: "C \<in> sys_xcpts"
shows "\<not>P \<turnstile> C \<preceq>\<^sup>* Start"
proof -
  have Cns: "C \<noteq> Start" using Start_nsys_xcpts sx by clarsimp
  show ?thesis using wf_subcls_nCls[OF wf ns _ Cns] by auto
qed

end
