(*  Title: JinjaDCI/BV/ClassAdd.thy
    Author:     Susannah Mansky
    2018, UIUC
*)
(* Preservation of various properties when adding a class to a program *)

theory ClassAdd
imports BVConform
begin

(* HERE: MOVE *)
lemma err_mono: "A \<subseteq> B \<Longrightarrow> err A \<subseteq> err B"
 by(unfold err_def) auto

lemma opt_mono: "A \<subseteq> B \<Longrightarrow> opt A \<subseteq> opt B"
 by(unfold opt_def) auto

(* HERE: MOVE ! ! *)
lemma Object_fields:
 "\<lbrakk> P \<turnstile> Object has_fields FDTs; C \<noteq> Object \<rbrakk> \<Longrightarrow> map_of FDTs (F,C) = None"
 by(drule Fields.cases, auto simp: map_of_reinsert_neq_None)

(* HERE: MOVE! *)
lemma has_fields_is_class_Object:
 "P \<turnstile> D has_fields FDTs \<Longrightarrow> is_class P Object"
 by(induct rule: Fields.induct; simp add: is_class_def)

(* HERE: MOVE! *)
lemma sees_methods_is_class_Object:
 "P \<turnstile> D sees_methods Mm \<Longrightarrow> is_class P Object"
 by(induct rule: Methods.induct; simp add: is_class_def)

(******************)

abbreviation class_add :: "jvm_prog \<Rightarrow> jvm_method cdecl \<Rightarrow> jvm_prog" where
"class_add P cd \<equiv> cd#P"

lemma class_add_has_fields:
assumes fs: "P \<turnstile> D has_fields FDTs" and nc: "\<not>is_class P C"
shows "class_add P (C, cdec) \<turnstile> D has_fields FDTs"
using assms
proof(induct rule: Fields.induct)
  case (has_fields_Object D fs ms FDTs)
  from has_fields_is_class_Object[OF fs] nc have "C \<noteq> Object" by fast
  with has_fields_Object show ?case
   by(auto simp: class_def fun_upd_apply intro!: TypeRel.has_fields_Object)
next
  case rec: (has_fields_rec C1 D fs ms FDTs FDTs')
  with has_fields_is_class have [simp]: "D \<noteq> C" by auto
  with rec have "C1 \<noteq> C" by(clarsimp simp: is_class_def)
  with rec show ?case
   by(auto simp: class_def fun_upd_apply intro: TypeRel.has_fields_rec)
qed

lemma class_add_has_fields_rev:
 "\<lbrakk> class_add P (C, cdec) \<turnstile> D has_fields FDTs; \<not>P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
 \<Longrightarrow> P \<turnstile> D has_fields FDTs"
proof(induct rule: Fields.induct)
  case (has_fields_Object D fs ms FDTs)
  then show ?case by(auto simp: class_def fun_upd_apply intro!: TypeRel.has_fields_Object)
next
  case rec: (has_fields_rec C1 D fs ms FDTs FDTs')
  then have sub1: "P \<turnstile> C1 \<prec>\<^sup>1 D"
   by(auto simp: class_def fun_upd_apply intro!: subcls1I split: if_split_asm)
  with rec.prems have cls: "\<not> P \<turnstile> D \<preceq>\<^sup>* C" by (meson converse_rtrancl_into_rtrancl)
  with cls rec show ?case
   by(auto simp: class_def fun_upd_apply
           intro: TypeRel.has_fields_rec split: if_split_asm)
qed

lemma class_add_has_field:
assumes "P \<turnstile> C\<^sub>0 has F,b:T in D" and "\<not> is_class P C"
shows "class_add P (C, cdec) \<turnstile> C\<^sub>0 has F,b:T in D"
using assms by(auto simp: has_field_def dest!: class_add_has_fields[of P C\<^sub>0])

lemma class_add_has_field_rev:
assumes has: "class_add P (C, cdec) \<turnstile> C\<^sub>0 has F,b:T in D"
 and ncp: "\<And>D'. P \<turnstile> C\<^sub>0 \<preceq>\<^sup>* D' \<Longrightarrow> D' \<noteq> C"
shows "P \<turnstile> C\<^sub>0 has F,b:T in D"
using assms by(auto simp add: has_field_def dest!: class_add_has_fields_rev)

lemma class_add_sees_field:
assumes "P \<turnstile> C\<^sub>0 sees F,b:T in D" and "\<not> is_class P C"
shows "class_add P (C, cdec) \<turnstile> C\<^sub>0 sees F,b:T in D"
using assms by(auto simp: sees_field_def dest!: class_add_has_fields[of P C\<^sub>0])

lemma class_add_sees_field_rev:
assumes has: "class_add P (C, cdec) \<turnstile> C\<^sub>0 sees F,b:T in D"
 and ncp: "\<And>D'. P \<turnstile> C\<^sub>0 \<preceq>\<^sup>* D' \<Longrightarrow> D' \<noteq> C"
shows "P \<turnstile> C\<^sub>0 sees F,b:T in D"
using assms by(auto simp add: sees_field_def dest!: class_add_has_fields_rev)

lemma class_add_field:
assumes fd: "P \<turnstile> C\<^sub>0 sees F,b:T in D" and "\<not> is_class P C"
shows "field P C\<^sub>0 F = field (class_add P (C, cdec)) C\<^sub>0 F"
using class_add_sees_field[OF assms, of cdec] fd by simp

lemma class_add_sees_methods:
assumes ms: "P \<turnstile> D sees_methods Mm" and nc: "\<not>is_class P C"
shows "class_add P (C, cdec) \<turnstile> D sees_methods Mm"
using assms
proof(induct rule: Methods.induct)
  case (sees_methods_Object D fs ms Mm)
  from sees_methods_is_class_Object[OF ms] nc have "C \<noteq> Object" by fast
  with sees_methods_Object show ?case
   by(auto simp: class_def fun_upd_apply intro!: TypeRel.sees_methods_Object)
next
  case rec: (sees_methods_rec C1 D fs ms Mm Mm')
  with sees_methods_is_class have [simp]: "D \<noteq> C" by auto
  with rec have "C1 \<noteq> C" by(clarsimp simp: is_class_def)
  with rec show ?case
   by(auto simp: class_def fun_upd_apply intro: TypeRel.sees_methods_rec)
qed

lemma class_add_sees_methods_rev:
 "\<lbrakk> class_add P (C, cdec) \<turnstile> D sees_methods Mm;
    \<And>D'. P \<turnstile> D \<preceq>\<^sup>* D' \<Longrightarrow> D' \<noteq> C \<rbrakk>
 \<Longrightarrow> P \<turnstile> D sees_methods Mm"
proof(induct rule: Methods.induct)
  case (sees_methods_Object D fs ms Mm)
  then show ?case
   by(auto simp: class_def fun_upd_apply intro!: TypeRel.sees_methods_Object)
next
  case rec: (sees_methods_rec C1 D fs ms Mm Mm')
  then have sub1: "P \<turnstile> C1 \<prec>\<^sup>1 D"
   by(auto simp: class_def fun_upd_apply intro!: subcls1I)
  have cls: "\<And>D'. P \<turnstile> D \<preceq>\<^sup>* D' \<Longrightarrow> D' \<noteq> C"
  proof -
    fix D' assume "P \<turnstile> D \<preceq>\<^sup>* D'"
    with sub1 have "P \<turnstile> C1 \<preceq>\<^sup>* D'" by simp
    with rec.prems show "D' \<noteq> C" by simp
  qed
  with cls rec show ?case
   by(auto simp: class_def fun_upd_apply intro: TypeRel.sees_methods_rec)
qed

lemma class_add_sees_methods_Obj:
assumes "P \<turnstile> Object sees_methods Mm" and nObj: "C \<noteq> Object"
shows "class_add P (C, cdec) \<turnstile> Object sees_methods Mm"
proof -
  from assms obtain C' fs ms where cls: "class P Object = Some(C',fs,ms)"
     by(auto elim!: Methods.cases)
  with nObj have cls': "class (class_add P (C, cdec)) Object = Some(C',fs,ms)"
     by(simp add: class_def fun_upd_apply)
  from assms cls have "Mm = map_option (\<lambda>m. (m, Object)) \<circ> map_of ms" by(auto elim!: Methods.cases)
  with assms cls' show ?thesis
   by(auto simp: is_class_def fun_upd_apply intro!: sees_methods_Object)
qed

lemma class_add_sees_methods_rev_Obj:
assumes "class_add P (C, cdec) \<turnstile> Object sees_methods Mm" and nObj: "C \<noteq> Object"
shows "P \<turnstile> Object sees_methods Mm"
proof -
  from assms obtain C' fs ms where cls: "class (class_add P (C, cdec)) Object = Some(C',fs,ms)"
     by(auto elim!: Methods.cases)
  with nObj have cls': "class P Object = Some(C',fs,ms)"
     by(simp add: class_def fun_upd_apply)
  from assms cls have "Mm = map_option (\<lambda>m. (m, Object)) \<circ> map_of ms" by(auto elim!: Methods.cases)
  with assms cls' show ?thesis
   by(auto simp: is_class_def fun_upd_apply intro!: sees_methods_Object)
qed

lemma class_add_sees_method:
assumes "P \<turnstile> C\<^sub>0 sees M\<^sub>0, b : Ts\<rightarrow>T = m in D" and "\<not> is_class P C"
shows "class_add P (C, cdec) \<turnstile> C\<^sub>0 sees M\<^sub>0, b : Ts\<rightarrow>T = m in D"
using assms by(auto simp add: Method_def dest!: class_add_sees_methods[of P C\<^sub>0])

lemma class_add_method:
assumes md: "P \<turnstile> C\<^sub>0 sees M\<^sub>0, b : Ts\<rightarrow>T = m in D" and "\<not> is_class P C"
shows "method P C\<^sub>0 M\<^sub>0 = method (class_add P (C, cdec)) C\<^sub>0 M\<^sub>0"
using class_add_sees_method[OF assms, of cdec] md by simp

lemma class_add_sees_method_rev:
 "\<lbrakk> class_add P (C, cdec) \<turnstile> C\<^sub>0 sees M\<^sub>0, b : Ts\<rightarrow>T = m in D;
    \<not> P \<turnstile> C\<^sub>0 \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> C\<^sub>0 sees M\<^sub>0, b : Ts\<rightarrow>T = m in D"
 by(auto simp: Method_def dest!: class_add_sees_methods_rev)

lemma class_add_sees_method_Obj:
 "\<lbrakk> P \<turnstile> Object sees M\<^sub>0, b : Ts\<rightarrow>T = m in D; C \<noteq> Object \<rbrakk>
  \<Longrightarrow> class_add P (C, cdec) \<turnstile> Object sees M\<^sub>0, b : Ts\<rightarrow>T = m in D"
 by(auto simp add: Method_def dest!: class_add_sees_methods_Obj[where P=P])

lemma class_add_sees_method_rev_Obj:
 "\<lbrakk> class_add P (C, cdec) \<turnstile> Object sees M\<^sub>0, b : Ts\<rightarrow>T = m in D; C \<noteq> Object \<rbrakk>
  \<Longrightarrow> P \<turnstile> Object sees M\<^sub>0, b : Ts\<rightarrow>T = m in D"
 by(auto simp add: Method_def dest!: class_add_sees_methods_rev_Obj[where P=P])

lemma class_add_is_type:
 "is_type P T \<Longrightarrow> is_type (class_add P (C, cdec)) T"
 by(cases cdec, simp add: is_type_def is_class_def class_def fun_upd_apply split: ty.splits)

lemma class_add_types:
 "types P \<subseteq> types (class_add P (C, cdec))"
using class_add_is_type by(cases cdec, clarsimp)

lemma class_add_states:
 "states P mxs mxl \<subseteq> states (class_add P (C, cdec)) mxs mxl"
proof -
  let ?A = "types P" and ?B = "types (class_add P (C, cdec))"
  have "?A \<subseteq> ?B" by(rule class_add_types)
  then show ?thesis
  apply(clarsimp simp: JVM_states_unfold intro!: err_mono opt_mono)
  apply(unfold err_def list_def) apply(auto simp: Sigma_mono)
  proof - (* ACTUALLY : make this proof better *)
    fix a :: "ty list" and b :: "ty err list" and x :: "ty err"
    assume a1: "x \<noteq> Err"
    assume a2: "set b \<subseteq> insert Err {OK x |x. is_type P x}"
    assume a3: "x \<in> set b"
    assume a4: "types P \<subseteq> types (class_add P (C, cdec))"
    have f5: "\<exists>t. x = OK t \<and> is_type P t" using a3 a2 a1 by blast
    obtain tt :: "ty err \<Rightarrow> ty" where
      f6: "((\<nexists>t. x = OK t \<and> is_type P t) \<or> x = OK (tt x) \<and> is_type P (tt x)) \<and> ((\<exists>t. x = OK t \<and> is_type P t) \<or> (\<forall>t. x \<noteq> OK t \<or> \<not> is_type P t))"
      by moura
    then have "tt x \<in> types P"
      using f5 by blast
    then have "is_type (class_add P (C, cdec)) (tt x)"
      using a4 by blast
    then show "\<exists>t. x = OK t \<and> is_type (class_add P (C, cdec)) t"
      using f6 f5 by force
  qed
qed

lemma class_add_check_types:
 "check_types P mxs mxl \<tau>s \<Longrightarrow> check_types (class_add P (C, cdec)) mxs mxl \<tau>s"
using class_add_states by(fastforce simp: check_types_def)

lemma class_add_subcls:
 "\<lbrakk> P \<turnstile> D \<preceq>\<^sup>* D'; \<not> is_class P C \<rbrakk>
 \<Longrightarrow> class_add P (C, cdec) \<turnstile> D \<preceq>\<^sup>* D'"
proof(induct rule: rtrancl.induct)
  case (rtrancl_into_rtrancl a b c)
  then have "b \<noteq> C" by(clarsimp simp: is_class_def dest!: subcls1D)
  with rtrancl_into_rtrancl show ?case
   by(fastforce dest!: subcls1D simp: class_def fun_upd_apply
                intro!: rtrancl_trans[of a b] subcls1I)
qed(simp)

lemma class_add_subcls_rev:
 "\<lbrakk> class_add P (C, cdec) \<turnstile> D \<preceq>\<^sup>* D'; \<not>P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
 \<Longrightarrow> P \<turnstile> D \<preceq>\<^sup>* D'"
proof(induct rule: rtrancl.induct)
  case (rtrancl_into_rtrancl a b c)
  then have "b \<noteq> C" by(clarsimp simp: is_class_def dest!: subcls1D)
  with rtrancl_into_rtrancl show ?case
   by(fastforce dest!: subcls1D simp: class_def fun_upd_apply
                intro!: rtrancl_trans[of a b] subcls1I)
qed(simp)

lemma class_add_subtype:
 "\<lbrakk> subtype P x y; \<not> is_class P C \<rbrakk>
 \<Longrightarrow> subtype (class_add P (C, cdec)) x y"
proof(induct rule: widen.induct)
  case (widen_subcls C D)
  then show ?case using class_add_subcls by simp
qed(simp+)

lemma class_add_widens:
 "\<lbrakk> P \<turnstile> Ts [\<le>] Ts'; \<not> is_class P C \<rbrakk>
 \<Longrightarrow> (class_add P (C, cdec)) \<turnstile> Ts [\<le>] Ts'"
using class_add_subtype by (metis (no_types) list_all2_mono)

lemma class_add_sup_ty_opt:
 "\<lbrakk> P \<turnstile> l1 \<le>\<^sub>\<top> l2; \<not> is_class P C \<rbrakk>
  \<Longrightarrow> class_add P (C, cdec) \<turnstile> l1 \<le>\<^sub>\<top> l2"
using class_add_subtype by(auto simp: sup_ty_opt_def Err.le_def lesub_def split: err.splits)

lemma class_add_sup_loc:
"\<lbrakk> P \<turnstile> LT [\<le>\<^sub>\<top>] LT'; \<not> is_class P C \<rbrakk>
 \<Longrightarrow> class_add P (C, cdec) \<turnstile> LT [\<le>\<^sub>\<top>] LT'"
using class_add_sup_ty_opt[where P=P and C=C] by (simp add: list.rel_mono_strong)

lemma class_add_sup_state:
 "\<lbrakk> P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'; \<not> is_class P C \<rbrakk>
  \<Longrightarrow> class_add P (C, cdec) \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
using class_add_subtype class_add_sup_ty_opt
 by(auto simp: sup_state_def Listn.le_def Product.le_def lesub_def class_add_widens
               class_add_sup_ty_opt list_all2_mono)

lemma class_add_sup_state_opt:
 "\<lbrakk> P \<turnstile> \<tau> \<le>' \<tau>'; \<not> is_class P C \<rbrakk>
 \<Longrightarrow> class_add P (C, cdec) \<turnstile> \<tau> \<le>' \<tau>'"
 by(auto simp: sup_state_opt_def Opt.le_def lesub_def class_add_widens
               class_add_sup_ty_opt list_all2_mono)

lemma class_add_wf_mdecl:
  "\<lbrakk> wf_mdecl wf_md P C\<^sub>0 md;
     \<And>C\<^sub>0 md. wf_md P C\<^sub>0 md \<Longrightarrow> wf_md (class_add P (C, cdec)) C\<^sub>0 md \<rbrakk>
  \<Longrightarrow> wf_mdecl wf_md (class_add P (C, cdec)) C\<^sub>0 md"
 by(clarsimp simp: wf_mdecl_def class_add_is_type)

lemma class_add_wf_mdecl':
assumes wfd: "wf_mdecl wf_md P C\<^sub>0 md"
  and ms: "(C\<^sub>0,S,fs,ms) \<in> set P" and md: "md \<in> set ms"
  and wf_md': "\<And>C\<^sub>0 S fs ms m.\<lbrakk>(C\<^sub>0,S,fs,ms) \<in> set P; m \<in> set ms\<rbrakk> \<Longrightarrow> wf_md' (class_add P (C, cdec)) C\<^sub>0 m"
shows "wf_mdecl wf_md' (class_add P (C, cdec)) C\<^sub>0 md"
using assms by(clarsimp simp: wf_mdecl_def class_add_is_type)

lemma class_add_wf_cdecl:
assumes wfcd: "wf_cdecl wf_md P cd" and cdP: "cd \<in> set P"
 and ncp: "\<not> P \<turnstile> fst cd \<preceq>\<^sup>* C" and dist: "distinct_fst P"
 and wfmd: "\<And>C\<^sub>0 md. wf_md P C\<^sub>0 md \<Longrightarrow> wf_md (class_add P (C, cdec)) C\<^sub>0 md"
 and nclass: "\<not> is_class P C"
shows "wf_cdecl wf_md (class_add P (C, cdec)) cd"
proof -
  let ?P = "class_add P (C, cdec)"
  obtain C1 D fs ms where [simp]: "cd = (C1,(D,fs,ms))" by(cases cd)
  from wfcd
  have "\<forall>f\<in>set fs. wf_fdecl ?P f" by(auto simp: wf_cdecl_def wf_fdecl_def class_add_is_type)
  moreover
  from wfcd wfmd class_add_wf_mdecl
  have "\<forall>m\<in>set ms. wf_mdecl wf_md ?P C1 m" by(auto simp: wf_cdecl_def)
  moreover
  have "C1 \<noteq> Object \<Longrightarrow> is_class ?P D \<and> \<not> ?P \<turnstile> D \<preceq>\<^sup>* C1
    \<and> (\<forall>(M,b,Ts,T,m)\<in>set ms.
        \<forall>D' b' Ts' T' m'. ?P \<turnstile> D sees M,b':Ts' \<rightarrow> T' = m' in D' \<longrightarrow>
                       b = b' \<and> ?P \<turnstile> Ts' [\<le>] Ts \<and> ?P \<turnstile> T \<le> T')"
  proof -
    assume nObj[simp]: "C1 \<noteq> Object"
    with cdP dist have sub1: "P \<turnstile> C1 \<prec>\<^sup>1 D" by(auto simp: class_def intro!: subcls1I map_of_SomeI)
    with ncp have ncp': "\<not> P \<turnstile> D \<preceq>\<^sup>* C" by(auto simp: converse_rtrancl_into_rtrancl)
    with wfcd
    have clsD: "is_class ?P D"
     by(auto simp: wf_cdecl_def is_class_def class_def fun_upd_apply)
    moreover
    from wfcd sub1
    have "\<not> ?P \<turnstile> D \<preceq>\<^sup>* C1" by(auto simp: wf_cdecl_def dest!: class_add_subcls_rev[OF _ ncp'])
    moreover
    have "\<And>M b Ts T m D' b' Ts' T' m'. (M,b,Ts,T,m) \<in> set ms
            \<Longrightarrow> ?P \<turnstile> D sees M,b':Ts' \<rightarrow> T' = m' in D'
            \<Longrightarrow> b = b' \<and> ?P \<turnstile> Ts' [\<le>] Ts \<and> ?P \<turnstile> T \<le> T'"
    proof -
      fix M b Ts T m D' b' Ts' T' m'
      assume ms: "(M,b,Ts,T,m) \<in> set ms" and meth': "?P \<turnstile> D sees M,b':Ts' \<rightarrow> T' = m' in D'"
      with sub1
      have "P \<turnstile> D sees M,b':Ts' \<rightarrow> T' = m' in D'"
       by(fastforce dest!: class_add_sees_method_rev[OF _ ncp'])
      moreover
      with wfcd ms meth'
      have "b = b' \<and> P \<turnstile> Ts' [\<le>] Ts \<and> P \<turnstile> T \<le> T'"
       by(cases m', fastforce simp: wf_cdecl_def elim!: ballE[where x="(M,b,Ts,T,m)"])
      ultimately show "b = b' \<and> ?P \<turnstile> Ts' [\<le>] Ts \<and> ?P \<turnstile> T \<le> T'"
       by(auto dest!: class_add_subtype[OF _ nclass] class_add_widens[OF _ nclass])
    qed
    ultimately show ?thesis by clarsimp
  qed
  moreover note wfcd
  ultimately show ?thesis by(simp add: wf_cdecl_def)
qed

lemma class_add_wf_cdecl':
assumes wfcd: "wf_cdecl wf_md P cd" and cdP: "cd \<in> set P"
 and ncp: "\<not>P \<turnstile> fst cd \<preceq>\<^sup>* C" and dist: "distinct_fst P"
 and wfmd: "\<And>C\<^sub>0 S fs ms m.\<lbrakk>(C\<^sub>0,S,fs,ms) \<in> set P; m \<in> set ms\<rbrakk> \<Longrightarrow> wf_md' (class_add P (C, cdec)) C\<^sub>0 m"
 and nclass: "\<not> is_class P C"
shows "wf_cdecl wf_md' (class_add P (C, cdec)) cd"
proof -
  let ?P = "class_add P (C, cdec)"
  obtain C1 D fs ms where [simp]: "cd = (C1,(D,fs,ms))" by(cases cd)
  from wfcd
  have "\<forall>f\<in>set fs. wf_fdecl ?P f" by(auto simp: wf_cdecl_def wf_fdecl_def class_add_is_type)
  moreover
  from cdP wfcd wfmd
  have "\<forall>m\<in>set ms. wf_mdecl wf_md' ?P C1 m"
    by(auto simp: wf_cdecl_def wf_mdecl_def class_add_is_type)
  moreover
  have "C1 \<noteq> Object \<Longrightarrow> is_class ?P D \<and> \<not> ?P \<turnstile> D \<preceq>\<^sup>* C1
    \<and> (\<forall>(M,b,Ts,T,m)\<in>set ms.
        \<forall>D' b' Ts' T' m'. ?P \<turnstile> D sees M,b':Ts' \<rightarrow> T' = m' in D' \<longrightarrow>
                       b = b' \<and> ?P \<turnstile> Ts' [\<le>] Ts \<and> ?P \<turnstile> T \<le> T')"
  proof -
    assume nObj[simp]: "C1 \<noteq> Object"
    with cdP dist have sub1: "P \<turnstile> C1 \<prec>\<^sup>1 D" by(auto simp: class_def intro!: subcls1I map_of_SomeI)
    with ncp have ncp': "\<not> P \<turnstile> D \<preceq>\<^sup>* C" by(auto simp: converse_rtrancl_into_rtrancl)
    with wfcd
    have clsD: "is_class ?P D"
     by(auto simp: wf_cdecl_def is_class_def class_def fun_upd_apply)
    moreover
    from wfcd sub1
    have "\<not> ?P \<turnstile> D \<preceq>\<^sup>* C1" by(auto simp: wf_cdecl_def dest!: class_add_subcls_rev[OF _ ncp'])
    moreover
    have "\<And>M b Ts T m D' b' Ts' T' m'. (M,b,Ts,T,m) \<in> set ms
            \<Longrightarrow> ?P \<turnstile> D sees M,b':Ts' \<rightarrow> T' = m' in D'
            \<Longrightarrow> b = b' \<and> ?P \<turnstile> Ts' [\<le>] Ts \<and> ?P \<turnstile> T \<le> T'"
    proof -
      fix M b Ts T m D' b' Ts' T' m'
      assume ms: "(M,b,Ts,T,m) \<in> set ms" and meth': "?P \<turnstile> D sees M,b':Ts' \<rightarrow> T' = m' in D'"
      with sub1
      have "P \<turnstile> D sees M,b':Ts' \<rightarrow> T' = m' in D'"
       by(fastforce dest!: class_add_sees_method_rev[OF _ ncp'])
      moreover
      with wfcd ms meth'
      have "b = b' \<and> P \<turnstile> Ts' [\<le>] Ts \<and> P \<turnstile> T \<le> T'"
       by(cases m', fastforce simp: wf_cdecl_def elim!: ballE[where x="(M,b,Ts,T,m)"])
      ultimately show "b = b' \<and> ?P \<turnstile> Ts' [\<le>] Ts \<and> ?P \<turnstile> T \<le> T'"
       by(auto dest!: class_add_subtype[OF _ nclass] class_add_widens[OF _ nclass])
    qed
    ultimately show ?thesis by clarsimp
  qed
  moreover note wfcd
  ultimately show ?thesis by(simp add: wf_cdecl_def)
qed

lemma class_add_app\<^sub>i:
assumes "app\<^sub>i (i, P, pc, mxs, T\<^sub>r, ST, LT)" and "\<not> is_class P C"
shows "app\<^sub>i (i, class_add P (C, cdec), pc, mxs, T\<^sub>r, ST, LT)"
using assms
proof(cases i)
  case New then show ?thesis using assms by(fastforce simp: is_class_def class_def fun_upd_apply)
next
  case Getfield then show ?thesis using assms
   by(auto simp: class_add_subtype dest!: class_add_sees_field[where P=P])
next
  case Getstatic then show ?thesis using assms by(auto dest!: class_add_sees_field[where P=P])
next
  case Putfield then show ?thesis using assms
   by(auto dest!: class_add_subtype[where P=P] class_add_sees_field[where P=P])
next
  case Putstatic then show ?thesis using assms
   by(auto dest!: class_add_subtype[where P=P] class_add_sees_field[where P=P])
next
  case Checkcast then show ?thesis using assms
   by(clarsimp simp: is_class_def class_def fun_upd_apply)
next
  case Invoke then show ?thesis using assms
    by(fastforce dest!: class_add_widens[where P=P] class_add_sees_method[where P=P])
next
  case Invokestatic then show ?thesis using assms
    by(fastforce dest!: class_add_widens[where P=P] class_add_sees_method[where P=P])
next
  case Return then show ?thesis using assms by(clarsimp simp: class_add_subtype)
qed(simp+)

lemma class_add_wt_start:
 "\<lbrakk> wt_start P C\<^sub>0 b Ts mxl \<tau>s; \<not> is_class P C \<rbrakk>
 \<Longrightarrow> wt_start (class_add P (C, cdec)) C\<^sub>0 b Ts mxl \<tau>s"
using class_add_sup_state_opt by(clarsimp simp: wt_start_def split: staticb.splits)

lemma class_add_is_relevant_class:
 "\<lbrakk> is_relevant_class i P C\<^sub>0; \<not> is_class P C \<rbrakk>
  \<Longrightarrow> is_relevant_class i (class_add P (C, cdec)) C\<^sub>0"
  by(cases i, auto simp: class_add_subcls)

lemma class_add_is_relevant_class_rev:
assumes irc: "is_relevant_class i (class_add P (C, cdec)) C\<^sub>0"
  and ncp: "\<And>cd D'. cd \<in> set P \<Longrightarrow> \<not>P \<turnstile> fst cd \<preceq>\<^sup>* C"
  and wfxp: "wf_syscls P"
shows "is_relevant_class i P C\<^sub>0"
using assms
proof(cases i)
  case (Getfield F D) with assms
  show ?thesis by(fastforce simp: wf_syscls_def sys_xcpts_def dest!: class_add_subcls_rev)
next
  case (Putfield F D) with assms
  show ?thesis by(fastforce simp: wf_syscls_def sys_xcpts_def dest!: class_add_subcls_rev)
next
  case (Checkcast D) with assms
  show ?thesis by(fastforce simp: wf_syscls_def sys_xcpts_def dest!: class_add_subcls_rev)
qed(simp_all)

lemma class_add_is_relevant_entry:
 "\<lbrakk> is_relevant_entry P i pc e; \<not> is_class P C \<rbrakk>
  \<Longrightarrow> is_relevant_entry (class_add P (C, cdec)) i pc e"
 by(clarsimp simp: is_relevant_entry_def class_add_is_relevant_class)

lemma class_add_is_relevant_entry_rev:
 "\<lbrakk> is_relevant_entry (class_add P (C, cdec)) i pc e; 
    \<And>cd D'. cd \<in> set P \<Longrightarrow> \<not>P \<turnstile> fst cd \<preceq>\<^sup>* C;
    wf_syscls P \<rbrakk>
  \<Longrightarrow> is_relevant_entry P i pc e"
 by(auto simp: is_relevant_entry_def dest!: class_add_is_relevant_class_rev)

lemma class_add_relevant_entries:
 "\<not> is_class P C
  \<Longrightarrow> set (relevant_entries P i pc xt) \<subseteq> set (relevant_entries (class_add P (C, cdec)) i pc xt)"
 by(clarsimp simp: relevant_entries_def class_add_is_relevant_entry)

lemma class_add_relevant_entries_eq:
assumes wf: "wf_prog wf_md P" and nclass: "\<not> is_class P C"
shows "relevant_entries P i pc xt = relevant_entries (class_add P (C, cdec)) i pc xt"
proof -
  have ncp: "\<And>cd D'. cd \<in> set P \<Longrightarrow> \<not>P \<turnstile> fst cd \<preceq>\<^sup>* C"
   by(rule wf_subcls_nCls'[OF assms])
  moreover from wf have wfsys: "wf_syscls P" by(simp add: wf_prog_def)
  moreover
  note class_add_is_relevant_entry[OF _ nclass, of i pc _ cdec]
       class_add_is_relevant_entry_rev[OF _ ncp wfsys, of cdec i pc]
  ultimately show ?thesis by (metis filter_cong relevant_entries_def)
qed

lemma class_add_xcpt_app:
assumes xa: "xcpt_app i P pc mxs xt \<tau>"
 and wf: "wf_prog wf_md P" and nclass: "\<not> is_class P C"
shows "xcpt_app i (class_add P (C, cdec)) pc mxs xt \<tau>"
using xa class_add_relevant_entries_eq[OF wf nclass] nclass
 by(auto simp: xcpt_app_def is_class_def class_def fun_upd_apply) auto

lemma class_add_norm_eff_pc:
assumes ne: "\<forall>(pc',\<tau>') \<in> set (norm_eff i P pc \<tau>). pc' < mpc"
shows "\<forall>(pc',\<tau>') \<in> set (norm_eff i (class_add P (C, cdec)) pc \<tau>). pc' < mpc"
using assms by(cases i, auto simp: norm_eff_def)

lemma class_add_norm_eff_sup_state_opt:
assumes ne: "\<forall>(pc',\<tau>') \<in> set (norm_eff i P pc \<tau>). P \<turnstile> \<tau>' \<le>' \<tau>s!pc'"
   and nclass: "\<not> is_class P C" and app: "app\<^sub>i (i, P, pc, mxs, T, \<tau>)"
shows "\<forall>(pc',\<tau>') \<in> set (norm_eff i (class_add P (C, cdec)) pc \<tau>). (class_add P (C, cdec)) \<turnstile> \<tau>' \<le>' \<tau>s!pc'"
proof -
  obtain ST LT where "\<tau> = (ST,LT)" by(cases \<tau>)
  with assms show ?thesis proof(cases i)
  qed(fastforce simp: norm_eff_def
                dest!: class_add_field[where cdec=cdec] class_add_method[where cdec=cdec]
                       class_add_sup_loc[OF _ nclass] class_add_subtype[OF _ nclass]
                       class_add_widens[OF _ nclass] class_add_sup_state_opt[OF _ nclass])+
qed

lemma class_add_xcpt_eff_eq:
assumes wf: "wf_prog wf_md P" and nclass: "\<not> is_class P C"
shows "xcpt_eff i P pc \<tau> xt = xcpt_eff i (class_add P (C, cdec)) pc \<tau> xt"
using class_add_relevant_entries_eq[OF assms, of i pc xt cdec] by(cases \<tau>, simp add: xcpt_eff_def)

lemma class_add_eff_pc:
assumes eff: "\<forall>(pc',\<tau>') \<in> set (eff i P pc xt (Some \<tau>)). pc' < mpc"
  and wf: "wf_prog wf_md P" and nclass: "\<not> is_class P C"
shows "\<forall>(pc',\<tau>') \<in> set (eff i (class_add P (C, cdec)) pc xt (Some \<tau>)). pc' < mpc"
using eff class_add_norm_eff_pc class_add_xcpt_eff_eq[OF wf nclass]
  by(auto simp: norm_eff_def eff_def)

lemma class_add_eff_sup_state_opt:
assumes eff: "\<forall>(pc',\<tau>') \<in> set (eff i P pc xt (Some \<tau>)). P \<turnstile> \<tau>' \<le>' \<tau>s!pc'"
  and wf: "wf_prog wf_md P"and nclass: "\<not> is_class P C"
  and app: "app\<^sub>i (i, P, pc, mxs, T, \<tau>)"
shows "\<forall>(pc',\<tau>') \<in> set (eff i (class_add P (C, cdec)) pc xt (Some \<tau>)).
         (class_add P (C, cdec)) \<turnstile> \<tau>' \<le>' \<tau>s!pc'"
proof -
  from eff have ne: "\<forall>(pc', \<tau>')\<in>set (norm_eff i P pc \<tau>). P \<turnstile> \<tau>' \<le>' \<tau>s ! pc'"
   by(simp add: norm_eff_def eff_def)
  from eff have "\<forall>(pc', \<tau>')\<in>set (xcpt_eff i P pc \<tau> xt). P \<turnstile> \<tau>' \<le>' \<tau>s ! pc'"
   by(simp add: xcpt_eff_def eff_def)
  with class_add_norm_eff_sup_state_opt[OF ne nclass app]
       class_add_xcpt_eff_eq[OF wf nclass]class_add_sup_state_opt[OF _ nclass]
    show ?thesis by(cases cdec, auto simp: eff_def norm_eff_def xcpt_app_def)
qed

lemma class_add_app:
assumes app: "app i P mxs T pc mpc xt t"
 and wf: "wf_prog wf_md P" and nclass: "\<not> is_class P C"
shows "app i (class_add P (C, cdec)) mxs T pc mpc xt t"
proof(cases t)
  case (Some \<tau>)
  let ?P = "class_add P (C, cdec)"
  from assms Some have eff: "\<forall>(pc', \<tau>')\<in>set (eff i P pc xt \<lfloor>\<tau>\<rfloor>). pc' < mpc" by(simp add: app_def)
  from assms Some have app\<^sub>i: "app\<^sub>i (i,P,pc,mxs,T,\<tau>)" by(simp add: app_def)
  with class_add_app\<^sub>i[OF _ nclass] Some have "app\<^sub>i (i,?P,pc,mxs,T,\<tau>)" by(cases \<tau>,simp)
  moreover
  from app class_add_xcpt_app[OF _ wf nclass] Some
  have "xcpt_app i ?P pc mxs xt \<tau>" by(simp add: app_def del: xcpt_app_def)
  moreover
  from app class_add_eff_pc[OF eff wf nclass] Some
  have "\<forall>(pc',\<tau>') \<in> set (eff i ?P pc xt t). pc' < mpc" by auto
  moreover note app Some
  ultimately show ?thesis by(simp add: app_def)
qed(simp)

lemma class_add_wt_instr:
assumes wti: "P,T,mxs,mpc,xt \<turnstile> i,pc :: \<tau>s"
 and wf: "wf_prog wf_md P" and nclass: "\<not> is_class P C"
shows "class_add P (C, cdec),T,mxs,mpc,xt \<turnstile> i,pc :: \<tau>s"
proof -
  let ?P = "class_add P (C, cdec)"
  from wti have eff: "\<forall>(pc', \<tau>')\<in>set (eff i P pc xt (\<tau>s ! pc)). P \<turnstile> \<tau>' \<le>' \<tau>s ! pc'"
   by(simp add: wt_instr_def)
  from wti have app\<^sub>i: "\<tau>s!pc \<noteq> None \<Longrightarrow> app\<^sub>i (i,P,pc,mxs,T,the (\<tau>s!pc))"
   by(simp add: wt_instr_def app_def)
  from wti class_add_app[OF _ wf nclass]
  have "app i ?P mxs T pc mpc xt (\<tau>s!pc)" by(simp add: wt_instr_def)
  moreover
  have "\<forall>(pc',\<tau>') \<in> set (eff i ?P pc xt (\<tau>s!pc)). ?P \<turnstile> \<tau>' \<le>' \<tau>s!pc'"
  proof(cases "\<tau>s!pc")
    case Some with eff class_add_eff_sup_state_opt[OF _ wf nclass app\<^sub>i] show ?thesis by auto
  qed(simp add: eff_def)
  moreover note wti
  ultimately show ?thesis by(clarsimp simp: wt_instr_def)
qed

lemma class_add_wt_method:
assumes wtm: "wt_method P C\<^sub>0 b Ts T\<^sub>r mxs mxl\<^sub>0 is xt (\<Phi> C\<^sub>0 M\<^sub>0)"
 and wf: "wf_prog wf_md P" and nclass: "\<not> is_class P C"
shows "wt_method (class_add P (C, cdec)) C\<^sub>0 b Ts T\<^sub>r mxs mxl\<^sub>0 is xt (\<Phi> C\<^sub>0 M\<^sub>0)"
proof -
  let ?P = "class_add P (C, cdec)"
  let ?\<tau>s = "\<Phi> C\<^sub>0 M\<^sub>0"
  from wtm class_add_check_types
  have "check_types ?P mxs ((case b of Static \<Rightarrow> 0 | NonStatic \<Rightarrow> 1)+size Ts+mxl\<^sub>0) (map OK ?\<tau>s)"
   by(simp add: wt_method_def)
  moreover
  from wtm class_add_wt_start nclass
  have "wt_start ?P C\<^sub>0 b Ts mxl\<^sub>0 ?\<tau>s" by(simp add: wt_method_def)
  moreover
  from wtm class_add_wt_instr[OF _ wf nclass]
  have "\<forall>pc < size is. ?P,T\<^sub>r,mxs,size is,xt \<turnstile> is!pc,pc :: ?\<tau>s" by(clarsimp simp: wt_method_def)
  moreover note wtm
  ultimately
  show ?thesis by(clarsimp simp: wt_method_def)
qed

lemma class_add_wt_method':
 "\<lbrakk> (\<lambda>P C (M,b,Ts,T\<^sub>r,(mxs,mxl\<^sub>0,is,xt)). wt_method P C b Ts T\<^sub>r mxs mxl\<^sub>0 is xt (\<Phi> C M)) P C\<^sub>0 md;
    wf_prog wf_md P; \<not> is_class P C \<rbrakk>
    \<Longrightarrow> (\<lambda>P C (M,b,Ts,T\<^sub>r,(mxs,mxl\<^sub>0,is,xt)). wt_method P C b Ts T\<^sub>r mxs mxl\<^sub>0 is xt (\<Phi> C M))
            (class_add P (C, cdec)) C\<^sub>0 md"
 by(clarsimp simp: class_add_wt_method)

lemma class_add_distinct_fst:
"\<lbrakk> distinct_fst P; \<not> is_class P C \<rbrakk>
  \<Longrightarrow> distinct_fst (class_add P (C, cdec))"
 by(clarsimp simp add: distinct_fst_def is_class_def class_def)

(**********************************************)

(* HERE: MOVE *)
lemma class_add_classes_above:
assumes ns: "\<not> is_class P C" and "\<not>P \<turnstile> D \<preceq>\<^sup>* C"
shows "classes_above (class_add P (C, cdec)) D = classes_above P D"
using assms by(auto intro: class_add_subcls class_add_subcls_rev)

(* HERE: MOVE *)
lemma class_add_classes_above_xcpts:
assumes ns: "\<not> is_class P C"
 and ncp: "\<And>D. D \<in> sys_xcpts \<Longrightarrow> \<not>P \<turnstile> D \<preceq>\<^sup>* C"
shows "classes_above_xcpts (class_add P (C, cdec)) = classes_above_xcpts P"
using assms class_add_classes_above by simp

(*****************************************************************************)

(***)

(* HERE: MOVE ! ! *)
lemma class_add_conf:
 "\<lbrakk> P,h \<turnstile> v :\<le> T; \<not> is_class P C \<rbrakk>
 \<Longrightarrow> class_add P (C, cdec),h \<turnstile> v :\<le> T"
 by(clarsimp simp: conf_def class_add_subtype)

(* HERE: MOVE ! ! -- will not need fixes if above correct_state def *)
lemma class_add_oconf:
fixes obj::obj
assumes oc: "P,h \<turnstile> obj \<surd>" and ns: "\<not> is_class P C"
  and ncp: "\<And>D'. P \<turnstile> fst(obj) \<preceq>\<^sup>* D' \<Longrightarrow> D' \<noteq> C"
shows "(class_add P (C, cdec)),h \<turnstile> obj \<surd>"
proof -
  obtain C\<^sub>0 fs where [simp]: "obj=(C\<^sub>0,fs)" by(cases obj)
  from oc have
    oc': "\<And>F D T. P \<turnstile> C\<^sub>0 has F,NonStatic:T in D \<Longrightarrow> (\<exists>v. fs (F, D) = \<lfloor>v\<rfloor> \<and> P,h \<turnstile> v :\<le> T)"
    by(simp add: oconf_def)
  have "\<And>F D T. class_add P (C, cdec) \<turnstile> C\<^sub>0 has F,NonStatic:T in D
                       \<Longrightarrow> \<exists>v. fs(F,D) = Some v \<and> class_add P (C, cdec),h \<turnstile> v :\<le> T"
  proof -
    fix F D T assume "class_add P (C, cdec) \<turnstile> C\<^sub>0 has F,NonStatic:T in D"
    with class_add_has_field_rev[OF _ ncp] have meth: "P \<turnstile> C\<^sub>0 has F,NonStatic:T in D" by simp
    then show "\<exists>v. fs(F,D) = Some v \<and> class_add P (C, cdec),h \<turnstile> v :\<le> T"
    using oc'[OF meth] class_add_conf[OF _ ns] by(fastforce simp: oconf_def)
  qed
  then show ?thesis by(simp add: oconf_def)
qed

(* HERE: MOVE ! ! *)
lemma class_add_soconf:
assumes soc: "P,h,C\<^sub>0 \<turnstile>\<^sub>s sfs \<surd>" and ns: "\<not> is_class P C"
  and ncp: "\<And>D'. P \<turnstile> C\<^sub>0 \<preceq>\<^sup>* D' \<Longrightarrow> D' \<noteq> C"
shows "(class_add P (C, cdec)),h,C\<^sub>0 \<turnstile>\<^sub>s sfs \<surd>"
proof -
  from soc have
    oc': "\<And>F T. P \<turnstile> C\<^sub>0 has F,Static:T in C\<^sub>0 \<Longrightarrow> (\<exists>v. sfs F = \<lfloor>v\<rfloor> \<and> P,h \<turnstile> v :\<le> T)"
    by(simp add: soconf_def)
  have "\<And>F T. class_add P (C, cdec) \<turnstile> C\<^sub>0 has F,Static:T in C\<^sub>0
                       \<Longrightarrow> \<exists>v. sfs F = Some v \<and> class_add P (C, cdec),h \<turnstile> v :\<le> T"
  proof -
    fix F T assume "class_add P (C, cdec) \<turnstile> C\<^sub>0 has F,Static:T in C\<^sub>0"
    with class_add_has_field_rev[OF _ ncp] have meth: "P \<turnstile> C\<^sub>0 has F,Static:T in C\<^sub>0" by simp
    then show "\<exists>v. sfs F = Some v \<and> class_add P (C, cdec),h \<turnstile> v :\<le> T"
    using oc'[OF meth] class_add_conf[OF _ ns] by(fastforce simp: soconf_def)
  qed
  then show ?thesis by(simp add: soconf_def)
qed

lemma class_add_hconf:
assumes "P \<turnstile> h \<surd>" and "\<not> is_class P C"
 and "\<And>a obj D'. h a = Some obj \<Longrightarrow> P \<turnstile> fst(obj) \<preceq>\<^sup>* D' \<Longrightarrow> D' \<noteq> C"
shows "class_add P (C, cdec) \<turnstile> h \<surd>"
using assms by(auto simp: hconf_def intro!: class_add_oconf)

lemma class_add_hconf_wf:
assumes wf: "wf_prog wf_md P" and "P \<turnstile> h \<surd>" and "\<not> is_class P C"
 and "\<And>a obj. h a = Some obj \<Longrightarrow> fst(obj) \<noteq> C"
shows "class_add P (C, cdec) \<turnstile> h \<surd>"
using wf_subcls_nCls[OF wf] assms by(fastforce simp: hconf_def intro!: class_add_oconf)

lemma class_add_shconf:
assumes "P,h \<turnstile>\<^sub>s sh \<surd>" and ns: "\<not> is_class P C"
 and "\<And>C sobj D'. sh C = Some sobj \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D' \<Longrightarrow> D' \<noteq> C"
shows "class_add P (C, cdec),h \<turnstile>\<^sub>s sh \<surd>"
using assms by(fastforce simp: shconf_def)

lemma class_add_shconf_wf:
assumes wf: "wf_prog wf_md P" and "P,h \<turnstile>\<^sub>s sh \<surd>" and "\<not> is_class P C"
 and "\<And>C sobj. sh C = Some sobj \<Longrightarrow> C \<noteq> C"
shows "class_add P (C, cdec),h \<turnstile>\<^sub>s sh \<surd>"
using wf_subcls_nCls[OF wf] assms by(fastforce simp add: shconf_def)

(******************************************)

(* ACTUALLY: generalize
lemma class_add_wf_jvm_prog_phi:
assumes wtp: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
 and nclass: "\<not> is_class P C"
 and meth: "P \<turnstile> C sees M, Static :  []\<rightarrow>Void = m in D" and nclinit: "M \<noteq> clinit"
 and \<Phi>: "\<And>C'. C' \<noteq> C \<Longrightarrow> \<Phi>' C' = \<Phi> C'"
 and \<Phi>': "\<Phi>' C start_m = start_\<phi>\<^sub>m" "\<Phi>' C clinit = start_\<phi>\<^sub>m"
 and Obj_start_m: "\<And>b' Ts' T' m' D'. P \<turnstile> Object sees start_m, b' :  Ts'\<rightarrow>T' = m' in D'
         \<Longrightarrow> b' = Static \<and> Ts' = [] \<and> T' = Void"
shows "wf_jvm_prog\<^bsub>\<Phi>'\<^esub> (class_add P (C, cdec))"
proof -
  let ?wf_md = "(\<lambda>P C (M,b,Ts,T\<^sub>r,(mxs,mxl\<^sub>0,is,xt)). wt_method P C b Ts T\<^sub>r mxs mxl\<^sub>0 is xt (\<Phi> C M))"
  let ?wf_md' = "(\<lambda>P C (M,b,Ts,T\<^sub>r,(mxs,mxl\<^sub>0,is,xt)). wt_method P C b Ts T\<^sub>r mxs mxl\<^sub>0 is xt (\<Phi>' C M))"
  from wtp have wf: "wf_prog ?wf_md P" by(simp add: wf_jvm_prog_phi_def)
  from wf_subcls_nCls'[OF wf nclass]
  have ncp: "\<And>cd D'. cd \<in> set P \<Longrightarrow> \<not>P \<turnstile> fst cd \<preceq>\<^sup>* C" by simp
  have wf_md':
    "\<And>C\<^sub>0 S fs ms m. (C\<^sub>0, S, fs, ms) \<in> set P \<Longrightarrow> m \<in> set ms \<Longrightarrow> ?wf_md' (class_add P (C, cdec)) C\<^sub>0 m"
  proof -
    fix C\<^sub>0 S fs ms m assume asms: "(C\<^sub>0, S, fs, ms) \<in> set P" "m \<in> set ms"
    with nclass have ns: "C\<^sub>0 \<noteq> C" by(auto simp: is_class_def class_def dest: weak_map_of_SomeI)
    from wf asms have "?wf_md P C\<^sub>0 m" by(auto simp: wf_prog_def wf_cdecl_def wf_mdecl_def)

    with \<Phi>[OF ns] class_add_wt_method[OF _ wf nclass]
     show "?wf_md' (class_add P (C, cdec)) C\<^sub>0 m" by fastforce
  qed
  from wtp have a1: "is_class P Object" by (simp add: wf_jvm_prog_phi_def)
  with wf_sees_clinit[where P=P and C=Object] wtp
   have a2: "\<And>b' Ts' T' m' D'. P \<turnstile> Object sees clinit, b' :  Ts'\<rightarrow>T' = m' in D'
         \<Longrightarrow> b' = Static \<and> Ts' = [] \<and> T' = Void"
    by(fastforce simp: wf_jvm_prog_phi_def is_class_def dest: sees_method_fun)
  from wf have dist: "distinct_fst P" by (simp add: wf_prog_def)
  then have "distinct_fst (class_add P (C, cdec))" by(rule class_add_distinct_fst[OF _ nclass])
  moreover from wf have "wf_syscls (class_add P (C, cdec))" by(simp add: wf_prog_def wf_syscls_def)
  moreover
  from class_add_wf_cdecl'[where wf_md'="?wf_md'", OF _ _ ncp dist wf_md' nclass] wf
  have "\<And>c. c \<in> set P \<Longrightarrow> wf_cdecl ?wf_md' (class_add P (C, cdec)) c" by(auto simp: wf_prog_def)
  moreover from meth nclinit nclass \<Phi>' a1 Obj_start_m a2
  have "wf_cdecl ?wf_md' (class_add P (C, cdec)) (start_class C M)" by(simp add: start_class_wf)
  ultimately show ?thesis by(simp add: wf_jvm_prog_phi_def wf_prog_def)
qed

lemma class_add_wf_jvm_prog:
assumes wf: "wf_jvm_prog P"
 and nclass: "\<not> is_class P C"
 and meth: "P \<turnstile> C sees M, Static :  []\<rightarrow>Void = m in D" and nclinit: "M \<noteq> clinit"
 and Obj_start_m: "\<And>b' Ts' T' m' D'. P \<turnstile> Object sees start_m, b' :  Ts'\<rightarrow>T' = m' in D'
         \<Longrightarrow> b' = Static \<and> Ts' = [] \<and> T' = Void"
shows "wf_jvm_prog (class_add P (C, cdec))"
proof -
  from wf obtain \<Phi> where wtp: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P" by(clarsimp simp: wf_jvm_prog_def)

  let ?\<Phi>' = "\<lambda>C f. if C = C \<and> (f = start_m \<or> f = clinit) then start_\<phi>\<^sub>m else \<Phi> C f"

  from class_add_wf_jvm_prog_phi[OF wtp nclass meth nclinit _ _ _ Obj_start_m] have
    "wf_jvm_prog\<^bsub>?\<Phi>'\<^esub> (class_add P (C, cdec))" by simp
  then show ?thesis by(auto simp: wf_jvm_prog_def)
qed


lemma class_add_Start_sees_methods:
 "P \<turnstile> Object sees_methods Mm
 \<Longrightarrow> class_add P (C, cdec) \<turnstile>
  C sees_methods Mm ++ (map_option (\<lambda>m. (m,Start)) \<circ> map_of [start_method C M, start_clinit])"
 by (auto simp: start_class_def class_def fun_upd_apply
          dest!: class_add_sees_methods_Obj[of P] intro: sees_methods_rec)

lemma class_add_Start_sees_start_method:
 "P \<turnstile> Object sees_methods Mm
  \<Longrightarrow> class_add P (C, cdec) \<turnstile>
         C sees start_m, Static : []\<rightarrow>Void = (1, 0, [Invokestatic C M 0,Return], []) in C"
 by(auto simp: start_class_def start_method_def Method_def fun_upd_apply
         dest!: class_add_Start_sees_methods)

(* HERE: MOVE *)
lemma wf_class_add_Start_sees_start_method:
assumes wf: "wf_prog wf_md P"
shows "class_add P (C, cdec) \<turnstile>
         C sees start_m, Static : []\<rightarrow>Void = (1, 0, [Invokestatic C M 0,Return], []) in C"
proof -
  from wf have "is_class P Object" by simp
  with sees_methods_Object  obtain Mm where "P \<turnstile> Object sees_methods Mm"
   by(fastforce simp: is_class_def dest: sees_methods_Object)
  then show ?thesis by(rule class_add_Start_sees_start_method)
qed

(* HERE: MOVE *)
lemma class_add_start_m_instrs:
assumes wf: "wf_prog wf_md P"
shows "(instrs_of (class_add P (C, cdec)) C start_m) = [Invokestatic C M 0, Return]"
proof -
  from wf_class_add_Start_sees_start_method[OF wf]
  have "class_add P (C, cdec) \<turnstile> C sees start_m, Static :
           []\<rightarrow>Void = (1,0,[Invokestatic C M 0,Return],[]) in C" by simp
  then show ?thesis by simp
qed


(* HERE: MOVE ? *)
lemma class_add_Start_fields:
 "class_add P (C, cdec) \<turnstile> C has_fields FDTs \<Longrightarrow> map_of FDTs (F, C) = None"
 by(drule Fields.cases, auto simp: start_class_def class_def fun_upd_apply Object_fields)

lemma class_add_Start_soconf:
 "(class_add P (C, cdec)),h,Start \<turnstile>\<^sub>s Map.empty \<surd>"
 by(simp add: soconf_def has_field_def class_add_Start_fields)

lemma class_add_start_shconf:
 "class_add P (C, cdec),start_heap P \<turnstile>\<^sub>s start_sheap \<surd>"
(*<*)
  apply (unfold shconf_def)
  apply (simp add: preallocated_start fun_upd_apply class_add_Start_soconf)
  done
(*>*)
*)

(*************************************)

end