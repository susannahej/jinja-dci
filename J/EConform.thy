(*  Title:      Jinja/J/EConform.thy
    Author:     Susannah Mansky
    2017, UIUC
*)

section {* Expression Conformance *}

theory EConform
imports SmallStep BigStep
begin

(* HERE: MOVE *)
lemma cons_to_append: "list \<noteq> [] \<longrightarrow> (\<exists>ls. a # list = ls @ [last list])"
 by (metis append_butlast_last_id last_ConsR list.simps(3))

subsection{*Expression Conformance*}

definition seeing_class :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> cname option" where
"seeing_class P C M =
  (if \<exists>Ts T m D. P \<turnstile> C sees M,Static:Ts\<rightarrow>T = m in D
 then Some (fst(method P C M))
 else None)"

lemma seeing_class_def2[simp]:
 "P \<turnstile> C sees M,Static:Ts\<rightarrow>T = m in D \<Longrightarrow> seeing_class P C M = Some D"
 by(fastforce simp: seeing_class_def)

fun init_class :: "'m prog \<Rightarrow> 'a exp \<Rightarrow> cname option" where
"init_class P (new C) = Some C" |
"init_class P (C\<bullet>\<^sub>sF{D}) = Some D" |
"init_class P (C\<bullet>\<^sub>sF{D}:=e\<^sub>2) = Some D" |
"init_class P (C\<bullet>\<^sub>sM(es)) = seeing_class P C M" |
"init_class _ _ = None"

lemma icheck_init_class: "icheck P C e \<Longrightarrow> init_class P e = \<lfloor>C\<rfloor>"
apply(induct e, auto) apply(rename_tac x1 x2 x3 x4)
apply(case_tac x4, auto)
done

(* exp to take next small step (in particular, subexp that may contain initialization *)
fun ss_exp :: "'a exp \<Rightarrow> 'a exp" and ss_exps :: "'a exp list \<Rightarrow> 'a exp option" where
  "ss_exp (new C) = new C"
| "ss_exp (Cast C e) = (case val_of e of Some v \<Rightarrow> Cast C e | _ \<Rightarrow> ss_exp e)"
| "ss_exp (Val v) = Val v"
| "ss_exp (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) = (case val_of e\<^sub>1 of Some v \<Rightarrow> (case val_of e\<^sub>2 of Some v \<Rightarrow> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 | _ \<Rightarrow> ss_exp e\<^sub>2)
                                    | _ \<Rightarrow> ss_exp e\<^sub>1)"
| "ss_exp (Var V) = Var V"
| "ss_exp (LAss V e) = (case val_of e of Some v \<Rightarrow> LAss V e | _ \<Rightarrow> ss_exp e)"
| "ss_exp (e\<bullet>F{D}) = (case val_of e of Some v \<Rightarrow> e\<bullet>F{D} | _ \<Rightarrow> ss_exp e)"
| "ss_exp (C\<bullet>\<^sub>sF{D}) = C\<bullet>\<^sub>sF{D}"
| "ss_exp (e\<^sub>1\<bullet>F{D}:=e\<^sub>2) = (case val_of e\<^sub>1 of Some v \<Rightarrow> (case val_of e\<^sub>2 of Some v \<Rightarrow> e\<^sub>1\<bullet>F{D}:=e\<^sub>2 | _ \<Rightarrow> ss_exp e\<^sub>2)
                                    | _ \<Rightarrow> ss_exp e\<^sub>1)"
| "ss_exp (C\<bullet>\<^sub>sF{D}:=e\<^sub>2) = (case val_of e\<^sub>2 of Some v \<Rightarrow> C\<bullet>\<^sub>sF{D}:=e\<^sub>2 | _ \<Rightarrow> ss_exp e\<^sub>2)"
| "ss_exp (e\<bullet>M(es)) = (case val_of e of Some v \<Rightarrow> (case map_vals_of es of Some t \<Rightarrow> e\<bullet>M(es) | _ \<Rightarrow> the(ss_exps es))
                                    | _ \<Rightarrow> ss_exp e)"
| "ss_exp (C\<bullet>\<^sub>sM(es)) = (case map_vals_of es of Some t \<Rightarrow> C\<bullet>\<^sub>sM(es) | _ \<Rightarrow> the(ss_exps es))"
| "ss_exp ({V:T; e}) = ss_exp e"
| "ss_exp (e\<^sub>1;;e\<^sub>2) = (case val_of e\<^sub>1 of Some v \<Rightarrow> ss_exp e\<^sub>2
           | None \<Rightarrow> (case lass_val_of e\<^sub>1 of Some p \<Rightarrow> ss_exp e\<^sub>2
                                           | None \<Rightarrow> ss_exp e\<^sub>1))"
| "ss_exp (if (b) e\<^sub>1 else e\<^sub>2) = (case bool_of b of Some True \<Rightarrow> if (b) e\<^sub>1 else e\<^sub>2
                                        | Some False \<Rightarrow> if (b) e\<^sub>1 else e\<^sub>2
                                        | _ \<Rightarrow> ss_exp b)"
| "ss_exp (while (b) e) = while (b) e"
| "ss_exp (throw e) = (case val_of e of Some v \<Rightarrow> throw e | _ \<Rightarrow> ss_exp e)"
| "ss_exp (try e\<^sub>1 catch(C V) e\<^sub>2) = (case val_of e\<^sub>1 of Some v \<Rightarrow> try e\<^sub>1 catch(C V) e\<^sub>2
                                            | _ \<Rightarrow> ss_exp e\<^sub>1)"
| "ss_exp (INIT C (Cs,b) \<leftarrow> e) = INIT C (Cs,b) \<leftarrow> e"
| "ss_exp (RI (C,e);Cs \<leftarrow> e') = (case val_of e of Some v \<Rightarrow> RI (C,e);Cs \<leftarrow> e | _ \<Rightarrow> ss_exp e)"
| "ss_exps([]) = None"
| "ss_exps(e#es) = (case val_of e of Some v \<Rightarrow> ss_exps es | _ \<Rightarrow> Some (ss_exp e))"

(*<*)
lemmas ss_exp_ss_exps_induct = ss_exp_ss_exps.induct
 [ case_names New Cast Val BinOp Var LAss FAcc SFAcc FAss SFAss Call SCall
  Block Seq Cond While Throw Try Init RI Nil Cons ]
(*>*)

lemma icheck_ss_exp:
assumes "icheck P C e" shows "ss_exp e = e"
using assms
proof(cases e)
  case (SFAss C F D e) then show ?thesis using assms
  proof(cases e)qed(auto)
qed(auto)

lemma ss_exps_Vals_None[simp]:
 "ss_exps (map Val vs) = None"
 by(induct vs, auto)

lemma ss_exps_Vals_NoneI:
 "ss_exps es = None \<Longrightarrow> \<exists>vs. es = map Val vs"
 apply(induct es)
 using val_of_spec by auto

lemma ss_exps_throw_nVal:
 "\<lbrakk> val_of e = None; ss_exps (map Val vs @ throw e # es') = \<lfloor>e'\<rfloor> \<rbrakk>
   \<Longrightarrow> e' = ss_exp e"
 by(induct vs, auto)

lemma ss_exps_throw_Val:
 "\<lbrakk> val_of e = \<lfloor>a\<rfloor>; ss_exps (map Val vs @ throw e # es') = \<lfloor>e'\<rfloor> \<rbrakk>
   \<Longrightarrow> e' = throw e"
 by(induct vs, auto)


abbreviation curr_init :: "'m prog \<Rightarrow> 'a exp \<Rightarrow> cname option" where
"curr_init P e \<equiv> init_class P (ss_exp e)"
abbreviation curr_inits :: "'m prog \<Rightarrow> 'a exp list \<Rightarrow> cname option" where
"curr_inits P es \<equiv> case ss_exps es of Some e \<Rightarrow> init_class P e | _ \<Rightarrow> None"

lemma icheck_curr_init': "\<And>e'. ss_exp e = e' \<Longrightarrow> icheck P C e' \<Longrightarrow> curr_init P e = \<lfloor>C\<rfloor>"
 and icheck_curr_inits': "\<And>e. ss_exps es = \<lfloor>e\<rfloor> \<Longrightarrow> icheck P C e \<Longrightarrow> curr_inits P es = \<lfloor>C\<rfloor>"
proof(induct rule: ss_exp_ss_exps_induct)
qed(simp_all add: icheck_init_class)

lemma icheck_curr_init: "icheck P C e' \<Longrightarrow> ss_exp e = e' \<Longrightarrow> curr_init P e = \<lfloor>C\<rfloor>"
 by(rule icheck_curr_init')

lemma icheck_curr_inits: "icheck P C e \<Longrightarrow> ss_exps es = \<lfloor>e\<rfloor> \<Longrightarrow> curr_inits P es = \<lfloor>C\<rfloor>"
 by(rule icheck_curr_inits')

definition initPD :: "sheap \<Rightarrow> cname \<Rightarrow> bool" where
"initPD sh C \<equiv> \<exists>sfs i. sh C = Some (sfs, i) \<and> (i = Done \<or> i = Processing)"

(* checks that INIT and RI conform and are only in the main computation *)
fun iconf :: "'m prog \<Rightarrow> sheap \<Rightarrow> 'a exp \<Rightarrow> bool" and iconfs :: "'m prog \<Rightarrow> sheap \<Rightarrow> 'a exp list \<Rightarrow> bool" where
  "iconf P sh (new C) = True"
| "iconf P sh (Cast C e) = iconf P sh e"
| "iconf P sh (Val v) = True"
| "iconf P sh (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) = (case val_of e\<^sub>1 of Some v \<Rightarrow> iconf P sh e\<^sub>2 | _ \<Rightarrow> iconf P sh e\<^sub>1 \<and> \<not>sub_RI e\<^sub>2)"
| "iconf P sh (Var V) = True"
| "iconf P sh (LAss V e) = iconf P sh e"
| "iconf P sh (e\<bullet>F{D}) = iconf P sh e"
| "iconf P sh (C\<bullet>\<^sub>sF{D}) = True"
| "iconf P sh (e\<^sub>1\<bullet>F{D}:=e\<^sub>2) = (case val_of e\<^sub>1 of Some v \<Rightarrow> iconf P sh e\<^sub>2 | _ \<Rightarrow> iconf P sh e\<^sub>1 \<and> \<not>sub_RI e\<^sub>2)"
| "iconf P sh (C\<bullet>\<^sub>sF{D}:=e\<^sub>2) = iconf P sh e\<^sub>2"
| "iconf P sh (e\<bullet>M(es)) = (case val_of e of Some v \<Rightarrow> iconfs P sh es | _ \<Rightarrow> iconf P sh e \<and> \<not>sub_RIs es)"
| "iconf P sh (C\<bullet>\<^sub>sM(es)) = iconfs P sh es"
| "iconf P sh ({V:T; e}) = iconf P sh e"
| "iconf P sh (e\<^sub>1;;e\<^sub>2) = (case val_of e\<^sub>1 of Some v \<Rightarrow> iconf P sh e\<^sub>2
           | None \<Rightarrow> (case lass_val_of e\<^sub>1 of Some p \<Rightarrow> iconf P sh e\<^sub>2
                                           | None \<Rightarrow> iconf P sh e\<^sub>1 \<and> \<not>sub_RI e\<^sub>2))"
| "iconf P sh (if (b) e\<^sub>1 else e\<^sub>2) = (iconf P sh b \<and> \<not>sub_RI e\<^sub>1 \<and> \<not>sub_RI e\<^sub>2)"
| "iconf P sh (while (b) e) = (\<not>sub_RI b \<and> \<not>sub_RI e)"
| "iconf P sh (throw e) = iconf P sh e"
| "iconf P sh (try e\<^sub>1 catch(C V) e\<^sub>2) = (iconf P sh e\<^sub>1 \<and> \<not>sub_RI e\<^sub>2)"
| "iconf P sh (INIT C (Cs,b) \<leftarrow> e) = ((case Cs of Nil \<Rightarrow> initPD sh C | C'#Cs' \<Rightarrow> last Cs = C) \<and> \<not>sub_RI e)"
| "iconf P sh (RI (C,e);Cs \<leftarrow> e') = (iconf P sh e \<and> \<not>sub_RI e')"
| "iconfs P sh ([]) = True"
| "iconfs P sh (e#es) = (case val_of e of Some v \<Rightarrow> iconfs P sh es | _ \<Rightarrow> iconf P sh e \<and> \<not>sub_RIs es)"

lemma iconfs_map_throw: "iconfs P sh (map Val vs @ throw e # es') \<Longrightarrow> iconf P sh e"
 by(induct vs,auto)

lemma nsub_RI_iconf_aux:
 "(\<not>sub_RI (e::'a exp) \<longrightarrow> (\<forall>e'. e' \<in> subexp e \<longrightarrow> \<not>sub_RI e' \<longrightarrow> iconf P sh e') \<longrightarrow> iconf P sh e)
 \<and> (\<not>sub_RIs (es::'a exp list) \<longrightarrow> (\<forall>e'. e' \<in> subexps es \<longrightarrow> \<not>sub_RI e' \<longrightarrow> iconf P sh e') \<longrightarrow> iconfs P sh es)"
proof(induct rule: sub_RI_sub_RIs.induct)
(*next
  case Block:(13 V T e')
  show ?case
  proof(cases "assigned V e'")
    case True
    then obtain v e2 where "e' = V:=Val v;;e2" by(clarsimp simp: assigned_def)
    then show ?thesis using Block True by clarsimp
  next
    case False then show ?thesis using Block by simp
  qed*)
qed(auto)

lemma nsub_RI_iconf_aux':
 "(\<And>e'. subexp_of e' e \<Longrightarrow> \<not>sub_RI e' \<longrightarrow> iconf P sh e') \<Longrightarrow> (\<not>sub_RI e \<Longrightarrow> iconf P sh e)"
 by(simp add: nsub_RI_iconf_aux)

lemma nsub_RI_iconf: "\<not>sub_RI e \<Longrightarrow> iconf P sh e"
apply(cut_tac e = e and R = "\<lambda>e. \<not>sub_RI e \<longrightarrow> iconf P sh e" in subexp_induct)
apply(rename_tac ea) apply(case_tac ea, simp_all)
apply(clarsimp simp: nsub_RI_iconf_aux)
done

lemma nsub_RIs_iconfs: "\<not>sub_RIs es \<Longrightarrow> iconfs P sh es"
apply(cut_tac es = es and R = "\<lambda>e. \<not>sub_RI e \<longrightarrow> iconf P sh e"
  and Rs = "\<lambda>es. \<not>sub_RIs es \<longrightarrow> iconfs P sh es" in subexps_induct)
apply(rename_tac esa) apply(case_tac esa, simp_all)
apply(clarsimp simp: nsub_RI_iconf_aux)+
done

lemma lass_val_of_iconf: "lass_val_of e = \<lfloor>a\<rfloor> \<Longrightarrow> iconf P sh e"
 by(drule lass_val_of_nsub_RI, erule nsub_RI_iconf)

lemma icheck_iconf:
assumes "icheck P C e" shows "iconf P sh e"
using assms
proof(cases e)
  case (SFAss C F D e) then show ?thesis using assms
  proof(cases e)qed(auto)
next
  case (SCall C M es) then show ?thesis using assms
    by (auto simp: nsub_RIs_iconfs)
next
qed(auto)
(* by(rule nsub_RI_iconf, rule icheck_nsub_RI, simp) *)


definition bconf :: "'m prog \<Rightarrow> sheap \<Rightarrow> 'a exp \<Rightarrow> bool \<Rightarrow> bool"  ("_,_ \<turnstile>\<^sub>b '(_,_') \<surd>" [51,51,0,0] 50)
where
  "P,sh \<turnstile>\<^sub>b (e,b) \<surd>  \<equiv> b \<longrightarrow> (\<exists>C. icheck P C (ss_exp e) \<and> initPD sh C)"

definition bconfs :: "'m prog \<Rightarrow> sheap \<Rightarrow> 'a exp list \<Rightarrow> bool \<Rightarrow> bool"  ("_,_ \<turnstile>\<^sub>b '(_,_') \<surd>" [51,51,0,0] 50)
where
  "P,sh \<turnstile>\<^sub>b (es,b) \<surd>  \<equiv> b \<longrightarrow> (\<exists>C. (icheck P C (the(ss_exps es))
                           \<and> (curr_inits P es = Some C) \<and> initPD sh C))"


subsection{*bconf helper lemmas*}

lemma bconf_nonVal[simp]:
 "P,sh \<turnstile>\<^sub>b (e,True) \<surd> \<Longrightarrow> val_of e = None"
 by(cases e, auto simp: bconf_def)

lemma bconfs_nonVals[simp]:
 "P,sh \<turnstile>\<^sub>b (es,True) \<surd> \<Longrightarrow> map_vals_of es = None"
 by(induct es, auto simp: bconfs_def)

lemma bconf_Cast[iff]:
 "P,sh \<turnstile>\<^sub>b (Cast C e,b) \<surd> \<longleftrightarrow> P,sh \<turnstile>\<^sub>b (e,b) \<surd>"
apply(unfold bconf_def, cases b, auto)
apply(drule val_of_spec, simp)+
done

lemma bconf_BinOp[iff]:
 "P,sh \<turnstile>\<^sub>b (e1 \<guillemotleft>bop\<guillemotright> e2,b) \<surd>
   \<longleftrightarrow> (case val_of e1 of Some v \<Rightarrow> P,sh \<turnstile>\<^sub>b (e2,b) \<surd> | _ \<Rightarrow> P,sh \<turnstile>\<^sub>b (e1,b) \<surd>)"
apply(unfold bconf_def, cases b, auto)
apply(drule val_of_spec, simp)+
done

lemma bconf_LAss[iff]:
 "P,sh \<turnstile>\<^sub>b (LAss V e,b) \<surd> \<longleftrightarrow> P,sh \<turnstile>\<^sub>b (e,b) \<surd>"
apply(unfold bconf_def, cases b, auto)
apply(drule val_of_spec, simp)+
done

lemma bconf_FAcc[iff]:
 "P,sh \<turnstile>\<^sub>b (e\<bullet>F{D},b) \<surd> \<longleftrightarrow> P,sh \<turnstile>\<^sub>b (e,b) \<surd>"
apply(unfold bconf_def, cases b, auto)
apply(drule val_of_spec, simp)+
done

lemma bconf_FAss[iff]:
 "P,sh \<turnstile>\<^sub>b (FAss e1 F D e2,b) \<surd>
   \<longleftrightarrow> (case val_of e1 of Some v \<Rightarrow> P,sh \<turnstile>\<^sub>b (e2,b) \<surd> | _ \<Rightarrow> P,sh \<turnstile>\<^sub>b (e1,b) \<surd>)"
apply(unfold bconf_def, cases b, auto)
apply(drule val_of_spec, simp)+
done

lemma bconf_SFAss[iff]:
"val_of e2 = None \<Longrightarrow> P,sh \<turnstile>\<^sub>b (SFAss C F D e2,b) \<surd> \<longleftrightarrow> P,sh \<turnstile>\<^sub>b (e2,b) \<surd>"
 by(unfold bconf_def, cases b, auto)

lemma bconfs_Vals[iff]:
 "P,sh \<turnstile>\<^sub>b (map Val vs, b) \<surd> \<longleftrightarrow> \<not> b"
 by(unfold bconfs_def, simp)

lemma bconf_Call[iff]:
 "P,sh \<turnstile>\<^sub>b (e\<bullet>M(es),b) \<surd>
   \<longleftrightarrow> (case val_of e of Some v \<Rightarrow> P,sh \<turnstile>\<^sub>b (es,b) \<surd> | _ \<Rightarrow> P,sh \<turnstile>\<^sub>b (e,b) \<surd>)"
proof(cases b)
  case True
  then show ?thesis
  proof(cases "ss_exps es")
    case None
    then obtain vs where "es = map Val vs" using ss_exps_Vals_NoneI by auto
    then have mv: "map_vals_of es = \<lfloor>vs\<rfloor>" by simp
    then show ?thesis by(auto simp: bconf_def, simp add: bconfs_def)
  next
    case (Some a)
    then show ?thesis by(auto simp: bconf_def, auto simp: bconfs_def icheck_init_class)
  qed
qed(simp add: bconf_def bconfs_def)

lemma bconf_SCall[iff]:
assumes mvn: "map_vals_of es = None"
shows "P,sh \<turnstile>\<^sub>b (C\<bullet>\<^sub>sM(es),b) \<surd> \<longleftrightarrow> P,sh \<turnstile>\<^sub>b (es,b) \<surd>"
proof(cases b)
  case True
  then show ?thesis
  proof(cases "ss_exps es")
    case None
      then have "\<exists>vs. es = map Val vs" using ss_exps_Vals_NoneI by auto
      then show ?thesis using mvn finals_def by clarsimp
    next
    case (Some a)
      then show ?thesis by(auto simp: bconf_def, auto simp: bconfs_def icheck_init_class)
    qed
qed(simp add: bconf_def bconfs_def)

lemma bconf_Cons[iff]:
 "P,sh \<turnstile>\<^sub>b (e#es,b) \<surd>
   \<longleftrightarrow> (case val_of e of Some v \<Rightarrow> P,sh \<turnstile>\<^sub>b (es,b) \<surd> | _ \<Rightarrow> P,sh \<turnstile>\<^sub>b (e,b) \<surd>)"
proof(cases b)
  case True
  then show ?thesis
  proof(cases "ss_exps es")
    case None
      then have "\<exists>vs. es = map Val vs" using ss_exps_Vals_NoneI by auto
      then show ?thesis using None by(auto simp: bconf_def bconfs_def icheck_init_class)
    next
    case (Some a)
      then show ?thesis by(auto simp: bconf_def bconfs_def icheck_init_class)
    qed
qed(simp add: bconf_def bconfs_def)

lemma bconf_InitBlock[iff]:
 "P,sh \<turnstile>\<^sub>b ({V:T; V:=Val v;; e\<^sub>2},b) \<surd> \<longleftrightarrow> P,sh \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>"
 by(unfold bconf_def, cases b, auto simp: assigned_def)
(*apply(drule val_of_spec, simp)+
done *)

lemma bconf_Block[iff]:
 "P,sh \<turnstile>\<^sub>b ({V:T; e},b) \<surd> \<longleftrightarrow> P,sh \<turnstile>\<^sub>b (e,b) \<surd>"
 by(unfold bconf_def, cases b, auto)

(*lemma bconf_Block2[iff]:
 "assigned V e \<Longrightarrow> P,sh \<turnstile>\<^sub>b ({V:T; e},b) \<surd> \<longleftrightarrow> P,sh \<turnstile>\<^sub>b (snd(the(seq_of e)),b) \<surd>"
proof -
  assume assm: "assigned V e"
  then obtain v e2 where "e = V:=Val v;;e2" by(clarsimp simp: assigned_def)
  then show ?thesis by simp
qed*)

lemma bconf_Seq[iff]:
 "P,sh \<turnstile>\<^sub>b (e1;;e2,b) \<surd>
   \<longleftrightarrow> (case val_of e1 of Some v \<Rightarrow> P,sh \<turnstile>\<^sub>b (e2,b) \<surd>
                             | _ \<Rightarrow> (case lass_val_of e1 of Some p \<Rightarrow> P,sh \<turnstile>\<^sub>b (e2,b) \<surd>
                                                          | None \<Rightarrow> P,sh \<turnstile>\<^sub>b (e1,b) \<surd>))" (* \<longleftrightarrow> P,sh \<turnstile>\<^sub>b (e1,b) \<surd>"*)
by(unfold bconf_def, cases b, auto dest: val_of_spec lass_val_of_spec)

lemma bconf_Cond[iff]:
 "P,sh \<turnstile>\<^sub>b (if (b) e\<^sub>1 else e\<^sub>2,b') \<surd> \<longleftrightarrow> P,sh \<turnstile>\<^sub>b (b,b') \<surd>"
apply(unfold bconf_def, cases "bool_of b") apply auto[1]
apply(rename_tac a) apply(case_tac a)
apply(simp, drule bool_of_specT) apply auto[1]
apply(simp, drule bool_of_specF) apply auto[1]
done

lemma bconf_While[iff]:
 "P,sh \<turnstile>\<^sub>b (while (b) e,b') \<surd> \<longleftrightarrow> \<not>b'"
 by(unfold bconf_def, cases b, auto)

lemma bconf_Throw[iff]:
 "P,sh \<turnstile>\<^sub>b (throw e,b) \<surd> \<longleftrightarrow> P,sh \<turnstile>\<^sub>b (e,b) \<surd>"
apply(unfold bconf_def, cases b, auto)
apply(drule val_of_spec, simp)+
done

lemma bconf_Try[iff]:
 "P,sh \<turnstile>\<^sub>b (try e\<^sub>1 catch(C V) e\<^sub>2,b) \<surd> \<longleftrightarrow> P,sh \<turnstile>\<^sub>b (e\<^sub>1,b) \<surd>"
apply(unfold bconf_def, cases b, auto)
apply(drule val_of_spec, simp)+
done

lemma bconf_INIT[iff]:
 "P,sh \<turnstile>\<^sub>b (INIT C (Cs,b') \<leftarrow> e,b) \<surd> \<longleftrightarrow> \<not>b"
 by(unfold bconf_def, cases b, auto)

lemma bconf_RI[iff]:
 "P,sh \<turnstile>\<^sub>b (RI(C,e);Cs \<leftarrow> e',b) \<surd> \<longleftrightarrow> P,sh \<turnstile>\<^sub>b (e,b) \<surd>"
apply(unfold bconf_def, cases b, auto)
apply(drule val_of_spec, simp)+
done

lemma bconfs_map_throw[iff]:
 "P,sh \<turnstile>\<^sub>b (map Val vs @ throw e # es',b) \<surd> \<longleftrightarrow> P,sh \<turnstile>\<^sub>b (e,b) \<surd>"
 by(induct vs, auto)

end