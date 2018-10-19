(*  Title:      Jinja/Common/TypeRel.thy
    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)
(*
  Expanded to include statics
  Susannah Mansky
  2016-17, UIUC
*)

section {* Relations between Jinja Types *}

theory TypeRel imports 
  "HOL-Library.Transitive_Closure_Table"
  Decl
  "../MapOfThy"
begin

subsection{* The subclass relations *}

inductive_set
  subcls1 :: "'m prog \<Rightarrow> (cname \<times> cname) set"
  and subcls1' :: "'m prog \<Rightarrow> [cname, cname] \<Rightarrow> bool" ("_ \<turnstile> _ \<prec>\<^sup>1 _" [71,71,71] 70)
  for P :: "'m prog"
where
  "P \<turnstile> C  \<prec>\<^sup>1 D \<equiv> (C,D) \<in> subcls1 P"
| subcls1I: "\<lbrakk>class P C = Some (D,rest); C \<noteq> Object\<rbrakk> \<Longrightarrow> P \<turnstile> C \<prec>\<^sup>1 D"

abbreviation
  subcls  :: "'m prog \<Rightarrow> [cname, cname] \<Rightarrow> bool" ("_ \<turnstile> _ \<preceq>\<^sup>* _"  [71,71,71] 70)
  where "P \<turnstile> C  \<preceq>\<^sup>*  D \<equiv> (C,D) \<in> (subcls1 P)\<^sup>*"

lemma subcls1D: "P \<turnstile> C \<prec>\<^sup>1 D \<Longrightarrow> C \<noteq> Object \<and> (\<exists>fs ms. class P C = Some (D,fs,ms))"
(*<*)by(erule subcls1.induct)(fastforce simp add:is_class_def)(*>*)

lemma [iff]: "\<not> P \<turnstile> Object \<prec>\<^sup>1 C"
(*<*)by(fastforce dest:subcls1D)(*>*)

lemma [iff]: "(P \<turnstile> Object \<preceq>\<^sup>* C) = (C = Object)"
(*<*)
apply(rule iffI)
 apply(erule converse_rtranclE)
  apply simp_all
done
(*>*)

lemma subcls1_def2:
  "subcls1 P =
     (SIGMA C:{C. is_class P C}. {D. C\<noteq>Object \<and> fst (the (class P C))=D})"
(*<*)
  by (fastforce simp:is_class_def dest: subcls1D elim: subcls1I)
(*>*)

lemma finite_subcls1: "finite (subcls1 P)"
(*<*)
apply (simp add: subcls1_def2)
apply(rule finite_SigmaI [OF finite_is_class])
apply(rule_tac B = "{fst (the (class P C))}" in finite_subset)
apply  auto
done
(*>*)

primrec supercls_lst :: "'m prog \<Rightarrow> cname list \<Rightarrow> bool" where
"supercls_lst P (C#Cs) = ((\<forall>C' \<in> set Cs. P \<turnstile> C' \<preceq>\<^sup>* C) \<and> supercls_lst P Cs)" |
"supercls_lst P [] = True"

lemma supercls_lst_app:
 "\<lbrakk> supercls_lst P (C#Cs); P \<turnstile> C \<preceq>\<^sup>* C' \<rbrakk> \<Longrightarrow> supercls_lst P (C'#C#Cs)"
 by auto
(*
lemma subcls_is_class: "(C,D) \<in> (subcls1 P)\<^sup>+ \<Longrightarrow> is_class P C"
apply (unfold is_class_def)
apply(erule trancl_trans_induct)
apply (auto dest!: subcls1D)
done

lemma subcls_is_class: "P \<turnstile> C \<preceq>\<^sup>* D \<Longrightarrow> is_class P D \<longrightarrow> is_class P C"
apply (unfold is_class_def)
apply (erule rtrancl_induct)
apply  (drule_tac [2] subcls1D)
apply  auto
done
*)

subsection{* The subtype relations *}

inductive
  widen   :: "'m prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ \<le> _"   [71,71,71] 70)
  for P :: "'m prog"
where
  widen_refl[iff]: "P \<turnstile> T \<le> T"
| widen_subcls: "P \<turnstile> C \<preceq>\<^sup>* D  \<Longrightarrow>  P \<turnstile> Class C \<le> Class D"
| widen_null[iff]: "P \<turnstile> NT \<le> Class C"

abbreviation
  widens :: "'m prog \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> bool"
    ("_ \<turnstile> _ [\<le>] _" [71,71,71] 70) where
  "widens P Ts Ts' \<equiv> list_all2 (widen P) Ts Ts'"

lemma [iff]: "(P \<turnstile> T \<le> Void) = (T = Void)"
(*<*)by (auto elim: widen.cases)(*>*)

lemma [iff]: "(P \<turnstile> T \<le> Boolean) = (T = Boolean)"
(*<*)by (auto elim: widen.cases)(*>*)

lemma [iff]: "(P \<turnstile> T \<le> Integer) = (T = Integer)"
(*<*)by (auto elim: widen.cases)(*>*)

lemma [iff]: "(P \<turnstile> Void \<le> T) = (T = Void)"
(*<*)by (auto elim: widen.cases)(*>*)

lemma [iff]: "(P \<turnstile> Boolean \<le> T) = (T = Boolean)"
(*<*)by (auto elim: widen.cases)(*>*)

lemma [iff]: "(P \<turnstile> Integer \<le> T) = (T = Integer)"
(*<*)by (auto elim: widen.cases)(*>*)


lemma Class_widen: "P \<turnstile> Class C \<le> T  \<Longrightarrow>  \<exists>D. T = Class D"
(*<*)
apply (ind_cases "P \<turnstile> Class C \<le> T")
apply auto
done
(*>*)

lemma [iff]: "(P \<turnstile> T \<le> NT) = (T = NT)"
(*<*)
apply(cases T)
apply(auto dest:Class_widen)
done
(*>*)

lemma Class_widen_Class [iff]: "(P \<turnstile> Class C \<le> Class D) = (P \<turnstile> C \<preceq>\<^sup>* D)"
(*<*)
apply (rule iffI)
apply (ind_cases "P \<turnstile> Class C \<le> Class D")
apply (auto elim: widen_subcls)
done
(*>*)

lemma widen_Class: "(P \<turnstile> T \<le> Class C) = (T = NT \<or> (\<exists>D. T = Class D \<and> P \<turnstile> D \<preceq>\<^sup>* C))"
(*<*)by(induct T, auto)(*>*)


lemma widen_trans[trans]: "\<lbrakk>P \<turnstile> S \<le> U; P \<turnstile> U \<le> T\<rbrakk> \<Longrightarrow> P \<turnstile> S \<le> T"
(*<*)
proof -
  assume "P\<turnstile>S \<le> U" thus "\<And>T. P \<turnstile> U \<le> T \<Longrightarrow> P \<turnstile> S \<le> T"
  proof induct
    case (widen_refl T T') thus "P \<turnstile> T \<le> T'" .
  next
    case (widen_subcls C D T)
    then obtain E where "T = Class E" by (blast dest: Class_widen)
    with widen_subcls show "P \<turnstile> Class C \<le> T" by (auto elim: rtrancl_trans)
  next
    case (widen_null C RT)
    then obtain D where "RT = Class D" by (blast dest: Class_widen)
    thus "P \<turnstile> NT \<le> RT" by auto
  qed
qed
(*>*)

lemma widens_trans [trans]: "\<lbrakk>P \<turnstile> Ss [\<le>] Ts; P \<turnstile> Ts [\<le>] Us\<rbrakk> \<Longrightarrow> P \<turnstile> Ss [\<le>] Us"
(*<*)by (rule list_all2_trans, rule widen_trans)(*>*)


(*<*)
lemmas widens_refl [iff] = list_all2_refl [of "widen P", OF widen_refl] for P
lemmas widens_Cons [iff] = list_all2_Cons1 [of "widen P"] for P
(*>*)


subsection{* Method lookup *}

inductive
  Methods :: "['m prog, cname, mname \<rightharpoonup> (staticb \<times> ty list \<times> ty \<times> 'm) \<times> cname] \<Rightarrow> bool"
                    ("_ \<turnstile> _ sees'_methods _" [51,51,51] 50)
  for P :: "'m prog"
where
  sees_methods_Object:
 "\<lbrakk> class P Object = Some(D,fs,ms); Mm = map_option (\<lambda>m. (m,Object)) \<circ> map_of ms \<rbrakk>
  \<Longrightarrow> P \<turnstile> Object sees_methods Mm"
| sees_methods_rec:
 "\<lbrakk> class P C = Some(D,fs,ms); C \<noteq> Object; P \<turnstile> D sees_methods Mm;
    Mm' = Mm ++ (map_option (\<lambda>m. (m,C)) \<circ> map_of ms) \<rbrakk>
  \<Longrightarrow> P \<turnstile> C sees_methods Mm'"

lemma sees_methods_fun:
assumes 1: "P \<turnstile> C sees_methods Mm"
shows "\<And>Mm'. P \<turnstile> C sees_methods Mm' \<Longrightarrow> Mm' = Mm"
 (*<*)
using 1
proof induct
  case (sees_methods_rec C D fs ms Dres Cres Cres')
  have "class": "class P C = Some (D, fs, ms)"
   and notObj: "C \<noteq> Object" and Dmethods: "P \<turnstile> D sees_methods Dres"
   and IH: "\<And>Dres'. P \<turnstile> D sees_methods Dres' \<Longrightarrow> Dres' = Dres"
   and Cres: "Cres = Dres ++ (map_option (\<lambda>m. (m,C)) \<circ> map_of ms)"
   and Cmethods': "P \<turnstile> C sees_methods Cres'" by fact+
  from Cmethods' notObj "class" obtain Dres'
    where Dmethods': "P \<turnstile> D sees_methods Dres'"
     and Cres': "Cres' = Dres' ++ (map_option (\<lambda>m. (m,C)) \<circ> map_of ms)"
    by(auto elim: Methods.cases)
  from Cres Cres' IH[OF Dmethods'] show "Cres' = Cres" by simp
next
  case sees_methods_Object thus ?case by(auto elim: Methods.cases)
qed
(*>*)

lemma visible_methods_exist:
  "P \<turnstile> C sees_methods Mm \<Longrightarrow> Mm M = Some(m,D) \<Longrightarrow>
   (\<exists>D' fs ms. class P D = Some(D',fs,ms) \<and> map_of ms M = Some m)"
 (*<*)by(induct rule:Methods.induct) auto(*>*)

lemma sees_methods_decl_above:
assumes Csees: "P \<turnstile> C sees_methods Mm"
shows "Mm M = Some(m,D) \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
 (*<*)
using Csees
proof induct
next
  case sees_methods_Object thus ?case by auto
next
  case sees_methods_rec thus ?case
    by(fastforce simp:map_option_case split:option.splits
                elim:converse_rtrancl_into_rtrancl[OF subcls1I])
qed
(*>*)

lemma sees_methods_idemp:
assumes Cmethods: "P \<turnstile> C sees_methods Mm"
shows "\<And>m D. Mm M = Some(m,D) \<Longrightarrow>
              \<exists>Mm'. (P \<turnstile> D sees_methods Mm') \<and> Mm' M = Some(m,D)"
(*<*)
using Cmethods
proof induct
  case sees_methods_Object thus ?case
    by(fastforce dest: Methods.sees_methods_Object)
next
  case sees_methods_rec thus ?case
    by(fastforce split:option.splits dest: Methods.sees_methods_rec)
qed
(*>*)

(*FIXME something wrong with induct: need to attache [consumes 1]
directly to proof of thm, declare does not work. *)

lemma sees_methods_decl_mono:
assumes sub: "P \<turnstile> C' \<preceq>\<^sup>* C"
shows "P \<turnstile> C sees_methods Mm \<Longrightarrow>
       \<exists>Mm' Mm\<^sub>2. P \<turnstile> C' sees_methods Mm' \<and> Mm' = Mm ++ Mm\<^sub>2 \<and>
                 (\<forall>M m D. Mm\<^sub>2 M = Some(m,D) \<longrightarrow> P \<turnstile> D \<preceq>\<^sup>* C)"
(*<*)
      (is "_ \<Longrightarrow> \<exists>Mm' Mm2. ?Q C' C Mm' Mm2")
using sub
proof (induct rule:converse_rtrancl_induct)
  assume "P \<turnstile> C sees_methods Mm"
  hence "?Q C C Mm Map.empty" by simp
  thus "\<exists>Mm' Mm2. ?Q C C Mm' Mm2" by blast
next
  fix C'' C'
  assume sub1: "P \<turnstile> C'' \<prec>\<^sup>1 C'" and sub: "P \<turnstile> C' \<preceq>\<^sup>* C"
  and IH: "P \<turnstile> C sees_methods Mm \<Longrightarrow>
           \<exists>Mm' Mm2. P \<turnstile> C' sees_methods Mm' \<and>
                Mm' = Mm ++ Mm2 \<and> (\<forall>M m D. Mm2 M = Some(m,D) \<longrightarrow> P \<turnstile> D \<preceq>\<^sup>* C)"
  and Csees: "P \<turnstile> C sees_methods Mm"
  from IH[OF Csees] obtain Mm' Mm2 where C'sees: "P \<turnstile> C' sees_methods Mm'"
    and Mm': "Mm' = Mm ++ Mm2"
    and subC:"\<forall>M m D. Mm2 M = Some(m,D) \<longrightarrow> P \<turnstile> D \<preceq>\<^sup>* C" by blast
  obtain fs ms where "class": "class P C'' = Some(C',fs,ms)" "C'' \<noteq> Object"
    using subcls1D[OF sub1] by blast
  let ?Mm3 = "map_option (\<lambda>m. (m,C'')) \<circ> map_of ms"
  have "P \<turnstile> C'' sees_methods (Mm ++ Mm2) ++ ?Mm3"
    using sees_methods_rec[OF "class" C'sees refl] Mm' by simp
  hence "?Q C'' C ((Mm ++ Mm2) ++ ?Mm3) (Mm2++?Mm3)"
    using converse_rtrancl_into_rtrancl[OF sub1 sub]
    by simp (simp add:map_add_def subC split:option.split)
  thus "\<exists>Mm' Mm2. ?Q C'' C Mm' Mm2" by blast
qed
(*>*)

definition Method :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> staticb \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'm \<Rightarrow> cname \<Rightarrow> bool"
            ("_ \<turnstile> _ sees _, _ :  _\<rightarrow>_ = _ in _" [51,51,51,51,51,51,51,51] 50)
where
  "P \<turnstile> C sees M, b: Ts\<rightarrow>T = m in D  \<equiv>
  \<exists>Mm. P \<turnstile> C sees_methods Mm \<and> Mm M = Some((b,Ts,T,m),D)"

definition has_method :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> staticb \<Rightarrow> bool"
            ("_ \<turnstile> _ has _, _" [51,0,51,51] 50)
where
  "P \<turnstile> C has M, b \<equiv> \<exists>Ts T m D b. P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D"

lemma sees_method_fun:
  "\<lbrakk>P \<turnstile> C sees M,b:TS\<rightarrow>T = m in D; P \<turnstile> C sees M,b':TS'\<rightarrow>T' = m' in D' \<rbrakk>
   \<Longrightarrow> b = b' \<and> TS' = TS \<and> T' = T \<and> m' = m \<and> D' = D"
 (*<*)by(fastforce dest: sees_methods_fun simp:Method_def)(*>*)

lemma sees_method_decl_above:
  "P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
 (*<*)by(clarsimp simp:Method_def sees_methods_decl_above)(*>*)

lemma visible_method_exists:
  "P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D \<Longrightarrow>
  \<exists>D' fs ms. class P D = Some(D',fs,ms) \<and> map_of ms M = Some(b,Ts,T,m)"
(*<*)by(fastforce simp:Method_def dest!: visible_methods_exist)(*>*)


lemma sees_method_idemp:
  "P \<turnstile> C sees M,b:Ts\<rightarrow>T=m in D \<Longrightarrow> P \<turnstile> D sees M,b:Ts\<rightarrow>T=m in D"
 (*<*)by(fastforce simp: Method_def intro:sees_methods_idemp)(*>*)

lemma sees_method_decl_mono:
  "\<lbrakk> P \<turnstile> C' \<preceq>\<^sup>* C; P \<turnstile> C sees M,b:Ts\<rightarrow>T=m in D;
     P \<turnstile> C' sees M,b':Ts'\<rightarrow>T'=m' in D' \<rbrakk> \<Longrightarrow> P \<turnstile> D' \<preceq>\<^sup>* D"
 (*<*)
apply(frule sees_method_decl_above)
apply(unfold Method_def)
apply clarsimp
apply(drule (1) sees_methods_decl_mono)
apply clarsimp
apply(drule (1) sees_methods_fun)
apply clarsimp
apply(blast intro:rtrancl_trans)
done
(*>*)

lemma sees_method_is_class:
  "\<lbrakk> P \<turnstile> C sees M,b:Ts\<rightarrow>T=m in D \<rbrakk> \<Longrightarrow> is_class P C"
(*<*)by (auto simp add: is_class_def Method_def elim: Methods.induct)(*>*)

lemma sees_method_is_class':
  "\<lbrakk> P \<turnstile> C sees M,b:Ts\<rightarrow>T=m in D \<rbrakk> \<Longrightarrow> is_class P D"
(*<*)by(drule sees_method_idemp, rule sees_method_is_class, assumption)(*>*)

subsection{* Field lookup *}

inductive
  Fields :: "['m prog, cname, ((vname \<times> cname) \<times> staticb \<times> ty) list] \<Rightarrow> bool"
                  ("_ \<turnstile> _ has'_fields _" [51,51,51] 50)
  for P :: "'m prog"
where
  has_fields_rec:
  "\<lbrakk> class P C = Some(D,fs,ms); C \<noteq> Object; P \<turnstile> D has_fields FDTs;
     FDTs' = map (\<lambda>(F,b,T). ((F,C),b,T)) fs @ FDTs \<rbrakk>
   \<Longrightarrow> P \<turnstile> C has_fields FDTs'"
| has_fields_Object:
  "\<lbrakk> class P Object = Some(D,fs,ms); FDTs = map (\<lambda>(F,b,T). ((F,Object),b,T)) fs \<rbrakk>
   \<Longrightarrow> P \<turnstile> Object has_fields FDTs"

lemma has_fields_is_class:
 "P \<turnstile> C has_fields FDTs \<Longrightarrow> is_class P C"
(*<*)by (auto simp add: is_class_def elim: Fields.induct)(*>*)

lemma has_fields_fun:
assumes 1: "P \<turnstile> C has_fields FDTs"
shows "\<And>FDTs'. P \<turnstile> C has_fields FDTs' \<Longrightarrow> FDTs' = FDTs"
 (*<*)
using 1
proof induct
  case (has_fields_rec C D fs ms Dres Cres Cres')
  have "class": "class P C = Some (D, fs, ms)"
   and notObj: "C \<noteq> Object" and DFields: "P \<turnstile> D has_fields Dres"
   and IH: "\<And>Dres'. P \<turnstile> D has_fields Dres' \<Longrightarrow> Dres' = Dres"
   and Cres: "Cres = map (\<lambda>(F,b,T). ((F,C),b,T)) fs @ Dres"
   and CFields': "P \<turnstile> C has_fields Cres'" by fact+
  from CFields' notObj "class" obtain Dres'
    where DFields': "P \<turnstile> D has_fields Dres'"
     and Cres': "Cres' = map (\<lambda>(F,b,T). ((F,C),b,T)) fs @ Dres'"
    by(auto elim: Fields.cases)
  from Cres Cres' IH[OF DFields'] show "Cres' = Cres" by simp
next
  case has_fields_Object thus ?case by(auto elim: Fields.cases)
qed
(*>*)

lemma all_fields_in_has_fields:
assumes sub: "P \<turnstile> C has_fields FDTs"
shows "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* D; class P D = Some(D',fs,ms); (F,b,T) \<in> set fs \<rbrakk>
       \<Longrightarrow> ((F,D),b,T) \<in> set FDTs"
(*<*)
using sub apply(induct, simp_all)
 apply(simp add:image_def)
 apply(erule converse_rtranclE)
  apply(force)
 apply(drule subcls1D)
 apply fastforce
apply(force simp:image_def)
done
(*>*)

lemma has_fields_decl_above:
assumes fields: "P \<turnstile> C has_fields FDTs"
shows "((F,D),b,T) \<in> set FDTs \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
(*<*)
using fields apply(induct)
 prefer 2 apply fastforce
apply clarsimp
apply(erule disjE)
 apply(clarsimp simp add:image_def)
apply simp
apply(blast dest:subcls1I converse_rtrancl_into_rtrancl)
done
(*>*)


lemma subcls_notin_has_fields:
assumes fields: "P \<turnstile> C has_fields FDTs"
shows "((F,D),b,T) \<in> set FDTs \<Longrightarrow> (D,C) \<notin> (subcls1 P)\<^sup>+"
(*<*)
using fields apply(induct)
 prefer 2 apply(fastforce dest: tranclD)
apply clarsimp
apply(erule disjE)
 apply(clarsimp simp add:image_def)
 apply(drule tranclD)
 apply clarify
 apply(frule subcls1D)
 apply(fastforce dest:all_fields_in_has_fields)
apply simp
apply(blast dest:subcls1I trancl_into_trancl)
done
(*>*)

lemma subcls_notin_has_fields2:
assumes fields: "P \<turnstile> C has_fields FDTs"
shows "\<lbrakk> C \<noteq> Object; P \<turnstile> C \<prec>\<^sup>1 D \<rbrakk> \<Longrightarrow> (D,C) \<notin> (subcls1 P)\<^sup>*"
using fields proof(induct arbitrary: D)
  case has_fields_rec
  have "\<forall>C C' P. (C, C') \<notin> subcls1 P \<or> C \<noteq> Object \<and> (\<exists>fs ms. class P C = \<lfloor>(C', fs, ms)\<rfloor>)"
    using subcls1D by blast
  then have "(D, D) \<notin> (subcls1 P)\<^sup>+"
    by (metis (no_types) Pair_inject has_fields_rec.hyps(1) has_fields_rec.hyps(4)
     has_fields_rec.prems(2) option.inject tranclD)
  then show ?case
    by (meson has_fields_rec.prems(2) rtrancl_into_trancl1)
qed(fastforce dest: tranclD)

lemma has_fields_mono_lem:
assumes sub: "P \<turnstile> D \<preceq>\<^sup>* C"
shows "P \<turnstile> C has_fields FDTs
         \<Longrightarrow> \<exists>pre. P \<turnstile> D has_fields pre@FDTs \<and> dom(map_of pre) \<inter> dom(map_of FDTs) = {}"
(*<*)
using sub apply(induct rule:converse_rtrancl_induct)
 apply(rule_tac x = "[]" in exI)
 apply simp
apply clarsimp
apply(rename_tac D' D pre)
apply(subgoal_tac "(D',C) : (subcls1 P)^+")
 prefer 2 apply(erule (1) rtrancl_into_trancl2)
apply(drule subcls1D)
apply clarsimp
apply(rename_tac fs ms)
apply(drule (2) has_fields_rec)
 apply(rule refl)
apply(rule_tac x = "map (\<lambda>(F,b,T). ((F,D'),b,T)) fs @ pre" in exI)
apply simp
apply(simp add:Int_Un_distrib2)
apply(rule equals0I)
apply(auto dest: subcls_notin_has_fields simp:dom_map_of_conv_image_fst image_def)
done
(*>*)

lemma has_fields_declaring_classes:
shows "P \<turnstile> C has_fields FDTs
         \<Longrightarrow> \<exists>pre FDTs'. FDTs = pre@FDTs'
                 \<and> (C \<noteq> Object \<longrightarrow> (\<exists>D fs ms. class P C = \<lfloor>(D,fs,ms)\<rfloor> \<and> P \<turnstile> D has_fields FDTs'))
                     \<and> set(map (\<lambda>t. snd(fst t)) pre) \<subseteq> {C}
                        \<and> set(map (\<lambda>t. snd(fst t)) FDTs') \<subseteq> {C'. C' \<noteq> C \<and> P \<turnstile> C \<preceq>\<^sup>* C'}"
proof(induct rule:Fields.induct)
  case (has_fields_rec C D fs ms FDTs FDTs')
  have sup1: "P \<turnstile> C \<prec>\<^sup>1 D" using has_fields_rec.hyps(1,2) by (simp add: subcls1.subcls1I)
  have "P \<turnstile> C has_fields FDTs'"
    using Fields.has_fields_rec[OF has_fields_rec.hyps(1-3)] has_fields_rec by auto
  then have nsup: "(D, C) \<notin> (subcls1 P)\<^sup>*" using subcls_notin_has_fields2 sup1 by auto
  show ?case using has_fields_rec sup1 nsup
    by(rule_tac x = "map (\<lambda>(F, y). ((F, C), y)) fs" in exI, clarsimp) auto
next
  case has_fields_Object then show ?case by fastforce
qed

lemma has_fields_mono_lem2:
assumes hf: "P \<turnstile> C has_fields FDTs"
 and cls: "class P C = Some(D,fs,ms)" and map_of: "map_of FDTs (F,C) = \<lfloor>(b,T)\<rfloor>"
shows "\<exists>FDTs'. FDTs = (map (\<lambda>(F,b,T). ((F,C),b,T)) fs) @ FDTs' \<and> map_of FDTs' (F,C) = None"
using assms
proof(cases "C = Object")
  case False
  let ?pre = "map (\<lambda>(F,b,T). ((F,C),b,T)) fs"
  have sub: "P \<turnstile> C \<preceq>\<^sup>* D" using cls False by (simp add: r_into_rtrancl subcls1.subcls1I)
  obtain FDTs' where fdts': "P \<turnstile> D has_fields FDTs' \<and> FDTs = ?pre @ FDTs'"
    using False assms(1,2) Fields.simps[of P C FDTs] by clarsimp
  then have int: "dom (map_of ?pre) \<inter> dom (map_of FDTs') = {}"
    using has_fields_mono_lem[OF sub, of FDTs'] has_fields_fun[OF hf] by fastforce
  have "C \<notin> (\<lambda>t. snd (fst t)) ` set FDTs'"
    using has_fields_declaring_classes[OF hf] cls False fdts'
      apply clarsimp apply(drule (1) has_fields_fun) by auto
  then have "map_of FDTs' (F,C) = None" by(rule map_of_set_pcs_notin)
  then show ?thesis using fdts' int by simp
qed(auto dest: has_fields_Object has_fields_fun)


(* FIXME why is Field not displayed correctly? TypeRel qualifier seems to confuse printer*)
definition has_field :: "'m prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> staticb \<Rightarrow> ty \<Rightarrow> cname \<Rightarrow> bool"
                   ("_ \<turnstile> _ has _,_:_ in _" [51,51,51,51,51,51] 50)
where
  "P \<turnstile> C has F,b:T in D  \<equiv>
  \<exists>FDTs. P \<turnstile> C has_fields FDTs \<and> map_of FDTs (F,D) = Some (b,T)"


lemma has_field_mono:
  "\<lbrakk> P \<turnstile> C has F,b:T in D; P \<turnstile> C' \<preceq>\<^sup>* C \<rbrakk> \<Longrightarrow> P \<turnstile> C' has F,b:T in D"
(*<*)
apply(clarsimp simp:has_field_def)
apply(drule (1) has_fields_mono_lem)
apply(fastforce simp: map_add_def split:option.splits)
done
(*>*)

lemma has_field_fun:
  "\<lbrakk>P \<turnstile> C has F,b:T in D; P \<turnstile> C has F,b':T' in D\<rbrakk> \<Longrightarrow> b = b' \<and> T' = T"
(*<*)by(fastforce simp:has_field_def dest:has_fields_fun)(*>*)

(* FIXME ugly *)  
lemma has_field_idemp:
  "P \<turnstile> C has F,b:T in D \<Longrightarrow> P \<turnstile> D has F,b:T in D"
(*<*)
  apply (unfold has_field_def)
  apply clarsimp
  apply (rule_tac P = "map_of xs (F,D) = y" for xs y in mp)
   prefer 2 
   apply assumption 
  apply (thin_tac "map_of xs (F,D) = y" for xs y)
  apply (erule Fields.induct)
   (* not Object *)
   apply clarsimp
   apply (frule map_of_SomeD)
   apply clarsimp
   apply (fastforce intro: has_fields_rec)
  (* Object *)
  apply clarsimp
  apply (frule map_of_SomeD)
  apply clarsimp
  apply (fastforce intro: has_fields_Object)
  done
(*>*)

lemma visible_fields_exist:
  "P \<turnstile> C has_fields FDTs \<Longrightarrow> map_of FDTs (F,D) = Some (b, T) \<Longrightarrow>
   (\<exists>D' fs ms. class P D = Some(D',fs,ms) \<and> map_of fs F = Some(b,T))"
apply (cut_tac
  Pa = "\<lambda>C FDTs. map_of FDTs (F,D) = Some (b, T) \<longrightarrow>
   (\<exists>D' fs ms. class P D = Some(D',fs,ms) \<and> map_of fs F = Some(b,T))"
  in Fields.induct, simp)
  apply clarsimp
  apply (case_tac "Ca = D")
   apply (simp, drule map_of_reinsert_SomeD, simp)
  apply (drule_tac D = D and F = F and fs = fs in map_of_reinsert_neq_None, simp)
 apply clarsimp
 apply (case_tac "Object = D")
  apply (simp, drule map_of_reinsert_SomeD, simp)
 apply (drule_tac D = D and F = F and fs = fs in map_of_reinsert_neq_None, simp)
apply simp
done

lemma map_of_remap_SomeD:
  "map_of (map (\<lambda>((k,k'),x). (k,(k',x))) t) k = Some (k',x) \<Longrightarrow> map_of t (k, k') = Some x"
(*<*)by (induct t) (auto simp:fun_upd_apply split: if_split_asm)(*>*)

lemma map_of_remap_SomeD2:
  "map_of (map (\<lambda>((k,k'),x,x'). (k,(k',x,x'))) t) k = Some (k',x,x') \<Longrightarrow> map_of t (k, k') = Some (x, x')"
(*<*)by (induct t) (auto simp:fun_upd_apply split: if_split_asm)(*>*)

lemma has_field_decl_above:
  "P \<turnstile> C has F,b:T in D \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
(*<*)
apply(auto simp:has_field_def)
apply(blast intro: has_fields_decl_above map_of_SomeD map_of_remap_SomeD2)
done
(*>*)

definition sees_field :: "'m prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> staticb \<Rightarrow> ty \<Rightarrow> cname \<Rightarrow> bool"
                  ("_ \<turnstile> _ sees _,_:_ in _" [51,51,51,51,51,51] 50)
where
  "P \<turnstile> C sees F,b:T in D \<equiv>
  \<exists>FDTs. P \<turnstile> C has_fields FDTs \<and>
            map_of (map (\<lambda>((F,D),b,T). (F,(D,b,T))) FDTs) F = Some(D,b,T)"

lemma has_visible_field:
  "P \<turnstile> C sees F,b:T in D \<Longrightarrow> P \<turnstile> C has F,b:T in D"
(*<*)by(auto simp add:has_field_def sees_field_def map_of_remap_SomeD2)(*>*)

lemma sees_field_fun:
  "\<lbrakk>P \<turnstile> C sees F,b:T in D; P \<turnstile> C sees F,b':T' in D'\<rbrakk> \<Longrightarrow> b = b' \<and> T' = T \<and> D' = D"
(*<*)by(fastforce simp:sees_field_def dest:has_fields_fun)(*>*)

lemma sees_field_decl_above:
  "P \<turnstile> C sees F,b:T in D \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
(*<*)
apply(auto simp:sees_field_def)
apply(blast intro: has_fields_decl_above map_of_SomeD map_of_remap_SomeD2)
done
(*>*)

(* FIXME ugly *)  
lemma sees_field_idemp:
  "P \<turnstile> C sees F,b:T in D \<Longrightarrow> P \<turnstile> D sees F,b:T in D"
(*<*)
  apply (unfold sees_field_def)
  apply clarsimp
  apply (rule_tac P = "map_of xs F = y" for xs y in mp)
   prefer 2 
   apply assumption 
  apply (thin_tac "map_of xs F = y" for xs y)
  apply (erule Fields.induct)
   (* not Object *)
   apply clarsimp
   apply (frule map_of_SomeD)
   apply clarsimp
   apply (fastforce intro: has_fields_rec)
  (* Object *)
  apply clarsimp
  apply (frule map_of_SomeD)
  apply clarsimp
  apply (fastforce intro: has_fields_Object)
  done
(*>*)

lemma has_field_sees_aux:
assumes hf: "P \<turnstile> C has_fields FDTs" and map: "map_of FDTs (F, C) = \<lfloor>(b, T)\<rfloor>"
shows "map_of (map (\<lambda>((F, D), b, T). (F, D, b, T)) FDTs) F = \<lfloor>(C, b, T)\<rfloor>"
proof -
  obtain D fs ms where fs: "class P C = Some(D,fs,ms)"
    using visible_fields_exist[OF assms] by clarsimp
  then obtain FDTs' where
     "FDTs = map (\<lambda>(F, b, T). ((F, C), b, T)) fs @ FDTs' \<and> map_of FDTs' (F, C) = None"
    using has_fields_mono_lem2[OF hf fs map] by clarsimp
  then show ?thesis using map_of_Some_None_split[OF _ _ map] by auto
qed

lemma has_field_sees: "P \<turnstile> C has F,b:T in C \<Longrightarrow> P \<turnstile> C sees F,b:T in C"
 by(auto simp:has_field_def sees_field_def has_field_sees_aux)

subsection "Functional lookup"

definition "method" :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> cname \<times> staticb \<times> ty list \<times> ty \<times> 'm"
where
  "method P C M \<equiv>  THE (D,b,Ts,T,m). P \<turnstile> C sees M,b:Ts \<rightarrow> T = m in D"

definition field  :: "'m prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> cname \<times> staticb \<times> ty"
where
  "field P C F  \<equiv>  THE (D,b,T). P \<turnstile> C sees F,b:T in D"
                                                        
definition fields :: "'m prog \<Rightarrow> cname \<Rightarrow> ((vname \<times> cname) \<times> staticb \<times> ty) list" 
where
  "fields P C  \<equiv>  THE FDTs. P \<turnstile> C has_fields FDTs"

lemma fields_def2 [simp]: "P \<turnstile> C has_fields FDTs \<Longrightarrow> fields P C = FDTs"
(*<*)by (unfold fields_def) (auto dest: has_fields_fun)(*>*)

lemma field_def2 [simp]: "P \<turnstile> C sees F,b:T in D \<Longrightarrow> field P C F = (D,b,T)"
(*<*)by (unfold field_def) (auto dest: sees_field_fun)(*>*)

lemma method_def2 [simp]: "P \<turnstile> C sees M,b: Ts\<rightarrow>T = m in D \<Longrightarrow> method P C M = (D,b,Ts,T,m)"
(*<*)by (unfold method_def) (auto dest: sees_method_fun)(*>*)

(* the two below are the fields for initializing an object (non-static fields) and
 a class (just that class's static fields), respectively *)
definition ifields :: "'m prog \<Rightarrow> cname \<Rightarrow> ((vname \<times> cname) \<times> staticb \<times> ty) list" 
where
  "ifields P C  \<equiv>  filter (\<lambda>((F,D),b,T). b = NonStatic) (fields P C)"

definition isfields :: "'m prog \<Rightarrow> cname \<Rightarrow> ((vname \<times> cname) \<times> staticb \<times> ty) list" 
where
  "isfields P C  \<equiv>  filter (\<lambda>((F,D),b,T). b = Static \<and> D = C) (fields P C)"

lemma ifields_def2[simp]: "\<lbrakk> P \<turnstile> C has_fields FDTs \<rbrakk> \<Longrightarrow> ifields P C = filter (\<lambda>((F,D),b,T). b = NonStatic) FDTs"
 by (simp add: ifields_def)

lemma isfields_def2[simp]: "\<lbrakk> P \<turnstile> C has_fields FDTs \<rbrakk> \<Longrightarrow> isfields P C = filter (\<lambda>((F,D),b,T). b = Static \<and> D = C) FDTs"
 by (simp add: isfields_def)

lemma ifields_def3: "\<lbrakk> P \<turnstile> C sees F,b:T in D; b = NonStatic \<rbrakk> \<Longrightarrow> (((F,D),b,T) \<in> set (ifields P C))"
(*<*) by (unfold ifields_def) (auto simp: sees_field_def map_of_SomeD map_of_remap_SomeD2) (*>*)

lemma isfields_def3: "\<lbrakk> P \<turnstile> C sees F,b:T in D; b = Static; D = C \<rbrakk> \<Longrightarrow> (((F,D),b,T) \<in> set (isfields P C))"
(*<*) by (unfold isfields_def) (auto simp: sees_field_def map_of_SomeD map_of_remap_SomeD2) (*>*)


lemma has_field_is_class:
 "P \<turnstile> C has F,b:T in D \<Longrightarrow> is_class P C"
(*<*)by (auto simp add: is_class_def has_field_def elim: Fields.induct)(*>*)

lemma has_field_is_class':
 "P \<turnstile> C has F,b:T in D \<Longrightarrow> is_class P D"
(*<*)by(drule has_field_idemp, rule has_field_is_class, assumption)(*>*)

subsection "Code generator setup"

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  subcls1p 
.
declare subcls1_def [code_pred_def]

code_pred 
  (modes: i \<Rightarrow> i \<times> o \<Rightarrow> bool, i \<Rightarrow> i \<times> i \<Rightarrow> bool)
  [inductify]
  subcls1 
.
definition subcls' where "subcls' G = (subcls1p G)^**"
code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  [inductify]
  subcls'
.

lemma subcls_conv_subcls' [code_unfold]:
  "(subcls1 G)^* = {(C, D). subcls' G C D}"
  by (simp add: subcls'_def subcls1_def rtrancl_def)

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  widen 
.

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  Fields
.

lemma has_field_code [code_pred_intro]:
  "\<lbrakk> P \<turnstile> C has_fields FDTs; map_of FDTs (F, D) = \<lfloor>(b,T)\<rfloor> \<rbrakk>
  \<Longrightarrow> P \<turnstile> C has F,b:T in D"
by(auto simp add: has_field_def)

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  has_field
by(auto simp add: has_field_def)

lemma sees_field_code [code_pred_intro]:
  "\<lbrakk> P \<turnstile> C has_fields FDTs; map_of (map (\<lambda>((F, D), b, T). (F, D, b, T)) FDTs) F = \<lfloor>(D, b, T)\<rfloor> \<rbrakk>
  \<Longrightarrow> P \<turnstile> C sees F,b:T in D"
by(auto simp add: sees_field_def)

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
          i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
          i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  sees_field
by(auto simp add: sees_field_def)

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  Methods
.

lemma Method_code [code_pred_intro]:
  "\<lbrakk> P \<turnstile> C sees_methods Mm; Mm M = \<lfloor>((b, Ts, T, m), D)\<rfloor> \<rbrakk>
  \<Longrightarrow> P \<turnstile> C sees M,b: Ts\<rightarrow>T = m in D"
by(auto simp add: Method_def)

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
          i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  Method
by(auto simp add: Method_def)

lemma eval_Method_i_i_i_o_o_o_o_o_conv:
  "Predicate.eval (Method_i_i_i_o_o_o_o_o P C M) = (\<lambda>(b, Ts, T, m, D). P \<turnstile> C sees M,b:Ts\<rightarrow>T=m in D)"
by(auto intro: Method_i_i_i_o_o_o_o_oI elim: Method_i_i_i_o_o_o_o_oE intro!: ext)

lemma method_code [code]:
  "method P C M = 
  Predicate.the (Predicate.bind (Method_i_i_i_o_o_o_o_o P C M) (\<lambda>(b, Ts, T, m, D). Predicate.single (D, b, Ts, T, m)))"
apply (rule sym, rule the_eqI)
apply (simp add: method_def eval_Method_i_i_i_o_o_o_o_o_conv)
apply (rule arg_cong [where f=The])
apply (auto simp add: Sup_fun_def Sup_bool_def fun_eq_iff)
done

lemma eval_Fields_conv:
  "Predicate.eval (Fields_i_i_o P C) = (\<lambda>FDTs. P \<turnstile> C has_fields FDTs)"
by(auto intro: Fields_i_i_oI elim: Fields_i_i_oE intro!: ext)

lemma fields_code [code]:
  "fields P C = Predicate.the (Fields_i_i_o P C)"
by(simp add: fields_def Predicate.the_def eval_Fields_conv)

lemma eval_sees_field_i_i_i_o_o_o_conv:
  "Predicate.eval (sees_field_i_i_i_o_o_o P C F) = (\<lambda>(b, T, D). P \<turnstile> C sees F,b:T in D)"
by(auto intro!: ext intro: sees_field_i_i_i_o_o_oI elim: sees_field_i_i_i_o_o_oE)

lemma eval_sees_field_i_i_i_o_o_i_conv:
  "Predicate.eval (sees_field_i_i_i_o_o_i P C F D) = (\<lambda>(b, T). P \<turnstile> C sees F,b:T in D)"
by(auto intro!: ext intro: sees_field_i_i_i_o_o_iI elim: sees_field_i_i_i_o_o_iE)

lemma eval_sees_field_i_i_i_o_i_i_conv:
  "Predicate.eval (sees_field_i_i_i_o_i_i P C F T D) = (\<lambda>b. P \<turnstile> C sees F,b:T in D)"
by(auto intro!: ext intro: sees_field_i_i_i_o_i_iI elim: sees_field_i_i_i_o_i_iE)

lemma eval_sees_field_i_i_i_i_o_i_conv:
  "Predicate.eval (sees_field_i_i_i_i_o_i P C F b D) = (\<lambda>T. P \<turnstile> C sees F,b:T in D)"
by(auto intro!: ext intro: sees_field_i_i_i_i_o_iI elim: sees_field_i_i_i_i_o_iE)

lemma field_code [code]:
  "field P C F = Predicate.the (Predicate.bind (sees_field_i_i_i_o_o_o P C F) (\<lambda>(b, T, D). Predicate.single (D, b, T)))"
apply (rule sym, rule the_eqI)
apply (simp add: field_def eval_sees_field_i_i_i_o_o_o_conv)
apply (rule arg_cong [where f=The])
apply (auto simp add: Sup_fun_def Sup_bool_def fun_eq_iff)
done

(*<*)
end
(*>*)