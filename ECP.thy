theory ECP
  imports Main
begin

type_synonym var = nat
type_synonym val = int
type_synonym env = "var \<Rightarrow> val"

definition lookup :: "env \<Rightarrow> var \<Rightarrow> val"
  where "lookup e var \<equiv> e var"

definition update :: "env \<Rightarrow> var \<Rightarrow> val \<Rightarrow> env"
  where "update e var v \<equiv> e(var := v)"

type_synonym precond = "env \<Rightarrow> bool"
type_synonym postcond = "env \<Rightarrow> env \<Rightarrow> bool"
type_synonym spec = "precond * postcond"

definition precond :: "spec \<Rightarrow> precond"
  where "precond \<equiv> fst"

definition postcond :: "spec \<Rightarrow> postcond"
  where "postcond \<equiv> snd"

type_synonym denotation = "env \<Rightarrow> env option"

datatype expr = Val val | Var var | Plus expr expr | Minus expr expr | IfExpr expr expr expr | Eq expr expr | Less expr expr | And expr expr | Or expr expr
datatype prog = Assn var expr | Seq prog prog | If expr prog prog

fun denoteExpr :: "expr \<Rightarrow> env \<Rightarrow> val option"
  where "denoteExpr (Val v) _ = Some v"
      | "denoteExpr (Var var) e = Some (lookup e var)"
      | "denoteExpr (Plus e1 e2) e = (case (denoteExpr e1 e, denoteExpr e2 e) of (Some v1, Some v2) \<Rightarrow> Some (v1 + v2) | _ \<Rightarrow> None)"
      | "denoteExpr (Minus e1 e2) e = (case (denoteExpr e1 e, denoteExpr e2 e) of (Some v1, Some v2) \<Rightarrow> Some (v1 - v2) | _ \<Rightarrow> None)"
      | "denoteExpr (IfExpr ec e1 e2) e = (case denoteExpr ec e of Some n \<Rightarrow> if n = 0 then denoteExpr e1 e else denoteExpr e2 e | None \<Rightarrow> None)"
      | "denoteExpr (Eq e1 e2) e = (case (denoteExpr e1 e, denoteExpr e2 e) of (Some v1, Some v2) \<Rightarrow> Some (if v1 = v2 then 1 else 0) | _ \<Rightarrow> None)"
      | "denoteExpr (Less e1 e2) e = (case (denoteExpr e1 e, denoteExpr e2 e) of (Some v1, Some v2) \<Rightarrow> Some (if v1 < v2 then 1 else 0) | _ \<Rightarrow> None)"
      | "denoteExpr (And e1 e2) e = (case (denoteExpr e1 e, denoteExpr e2 e) of (Some v1, Some v2) \<Rightarrow> Some (if v1 = 0 \<or> v2 = 0 then 0 else 1) | _ \<Rightarrow> None)"
      | "denoteExpr (Or e1 e2) e = (case (denoteExpr e1 e, denoteExpr e2 e) of (Some v1, Some v2) \<Rightarrow> Some (if v1 = 0 \<and> v2 = 0 then 0 else 1) | _ \<Rightarrow> None)"

fun denote :: "prog \<Rightarrow> denotation"
  where "denote (Assn var expr) e = (case denoteExpr expr e of Some v \<Rightarrow> Some (update e var v) | None \<Rightarrow> None)"
      | "denote (Seq prog1 prog2) e = (case denote prog1 e of Some e' \<Rightarrow> denote prog2 e' | None \<Rightarrow> None)"
      | "denote (If expr prog1 prog2) e = (case denoteExpr expr e of Some n \<Rightarrow> if n = 0 then denote prog1 e else denote prog2 e | None \<Rightarrow> None)"

definition "termination" :: "precond \<Rightarrow> prog \<Rightarrow> bool"
  where "termination pre prog \<equiv> \<forall>e. pre e \<longrightarrow> denote prog e \<noteq> None"

definition partiallyCorrect :: "spec \<Rightarrow> prog \<Rightarrow> bool"
  where "partiallyCorrect spec prog \<equiv> \<forall>e. precond spec e \<longrightarrow> (\<forall>e'. denote prog e = Some e' \<longrightarrow> postcond spec e e')"

definition totallyCorrect :: "spec \<Rightarrow> prog \<Rightarrow> bool"
  where "totallyCorrect spec prog \<equiv> termination (precond spec) prog \<and> partiallyCorrect spec prog"

definition test :: "spec \<Rightarrow> prog \<Rightarrow> env \<Rightarrow> bool"
  where "test spec prog e \<equiv> precond spec e \<longrightarrow> (\<exists>e'. denote prog e = Some e') \<and> postcond spec e (the (denote prog e))"

lemma totallyCorrect_iff: "totallyCorrect spec prog \<longleftrightarrow> (\<forall>e. test spec prog e)"
  unfolding totallyCorrect_def test_def termination_def partiallyCorrect_def by auto

definition defect :: "spec \<Rightarrow> prog \<Rightarrow> env \<Rightarrow> bool"
  where "defect spec prog e \<equiv> \<not> test spec prog e"

definition partitions :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool"
  where "partitions A As \<equiv> \<Union> As = A \<and> (\<forall>A1 \<in> As. \<forall>A2 \<in> As. A1 \<noteq> A2 \<longrightarrow> disjnt A1 A2) \<and> (\<forall>A' \<in> As. A' \<noteq> {})"

lemma nempty_partitions:
  assumes "A \<noteq> {}"
      and "partitions A As"
  shows "As \<noteq> {}"
using assms unfolding partitions_def by blast

definition representatives :: "'a set set \<Rightarrow> 'a set set" where
  "representatives X = {S. S \<subseteq> \<Union> X \<and> (\<forall>A \<in> X. (\<exists>x \<in> A. x \<in> S \<and> (\<forall>y \<in> A. y \<in> S \<longrightarrow> y = x)))}"

lemma representatives_exI: 
  assumes partitions: "partitions X Xs"
    and representatives: "X' \<in> representatives Xs"
    and P: "\<And>x. x \<in> X' \<Longrightarrow> P x"
    and X_mem: "X'' \<in> Xs"
  shows "\<exists>x \<in> X''. P x"
proof -
  have nempty_Xs: "Xs \<noteq> {}" using X_mem by blast
  have "X' \<noteq> {}" using representatives nempty_Xs unfolding representatives_def by blast
  obtain x where x_mem: "x \<in> X''" and x_mem': "x \<in> X'" using representatives unfolding representatives_def using X_mem by fastforce
  show "\<exists>x \<in> X''. P x" using x_mem P[OF x_mem'] by blast
qed

definition singletons :: "'a set \<Rightarrow> 'a set set"
  where "singletons A = (\<lambda>x. {x}) ` A"

lemma mem_singletonsD:
  assumes "x \<in> singletons X"
      and "y \<in> x"
      and "z \<in> x"
  shows "y = z"
using assms unfolding singletons_def by blast

lemma partitions_singletons:
  assumes nempty: "A \<noteq> {}"
  shows "partitions A (singletons A)"
unfolding partitions_def singletons_def by auto

lemma representatives_singletons:
  assumes nempty: "A \<noteq> {}"
  shows "representatives (singletons A) = {A}"
using assms unfolding representatives_def singletons_def by fastforce

locale domainTest =
  fixes possibleImpl :: "spec \<Rightarrow> prog set"
  assumes possibleImpl_ex_correct: "\<And>spec. \<exists>prog \<in> possibleImpl spec. totallyCorrect spec prog"
begin

definition ecp :: "spec \<Rightarrow> env set set \<Rightarrow> bool"
  where "ecp spec ess \<equiv> partitions (Collect (precond spec)) ess \<and> (\<forall>prog. prog \<in> possibleImpl spec \<longrightarrow> (\<forall>es. es \<in> ess \<longrightarrow> ((\<forall>e. e \<in> es \<longrightarrow> test spec prog e) \<or> (\<forall>e. e \<in> es \<longrightarrow> \<not> test spec prog e))))"  

lemma ecp_partitionsD:
  assumes "ecp spec ess"
  shows "partitions {e. precond spec e} ess"
using assms unfolding ecp_def by simp

lemma ecp_UnD:
  assumes "ecp spec ess"
  shows "\<Union> ess = {e. precond spec e}"
using assms unfolding ecp_def partitions_def by simp

lemma ecp_nempty:
  assumes ecp: "ecp spec ess"
      and mem: "es \<in> ess"
  shows "es \<noteq> {}"
using assms unfolding ecp_def partitions_def by simp

lemma ecp_singletons:
  assumes precond_nempty: "Collect (precond spec) \<noteq> {}"
  shows "ecp spec (singletons (Collect (precond spec)))"
unfolding ecp_def proof auto
  show "partitions {e. precond spec e} (singletons (Collect (precond spec)))" using precond_nempty by (rule partitions_singletons)
next
  fix e1 e2 :: env and es and prog
  assume "e1 \<in> es" and "e2 \<in> es" and "es \<in> singletons (Collect (precond spec))"
  hence eq: "e1 = e2" using mem_singletonsD by fastforce
  assume "\<not> test spec prog e1" "test spec prog e2"
  thus False unfolding eq by simp 
qed

(* それぞれの同値パーティションから任意の代表値を1つずつ選び、そのすべての代表値におけるテストが成功すれば完全正当性は成立する。 *)
lemma iff_totallyCorrect:
  assumes ecp: "ecp spec ess"
      and possibleImpl: "prog \<in> possibleImpl spec"
  shows "(\<forall>es \<in> ess. \<exists>e \<in> es. test spec prog e) \<longleftrightarrow> totallyCorrect spec prog"
proof
  assume success[rule_format]: "\<forall>es\<in>ess. \<exists>e \<in> es. test spec prog e"
  show "totallyCorrect spec prog" unfolding totallyCorrect_iff proof
    fix e
    show "test spec prog e" proof (cases "precond spec e")
      case True
      then obtain es where e_mem: "e \<in> es" and es_mem: "es \<in> ess" using ecp_UnD[OF ecp] by blast
      hence 1: "(\<forall>e. e \<in> es \<longrightarrow> test spec prog e) \<or> (\<forall>e. e \<in> es \<longrightarrow> \<not> test spec prog e)" using ecp possibleImpl unfolding ecp_def by simp
      have "\<not>(\<forall>e. e \<in> es \<longrightarrow> \<not> test spec prog e)" using success[OF es_mem] by blast
      thus ?thesis using 1 e_mem by blast
    next
      case False
      thus ?thesis unfolding test_def by simp
    qed
  qed
next
  assume totallyCorrect: "totallyCorrect spec prog"
  show "\<forall>es\<in>ess. \<exists>e \<in> es. test spec prog e" proof auto
    fix es
    assume es_mem: "es \<in> ess"
    obtain e where e_mem: "e \<in> es" using ecp_nempty[OF ecp, OF es_mem] by blast
    have success: "test spec prog e" using totallyCorrect unfolding totallyCorrect_iff by simp
    show "\<exists>e \<in> es. test spec prog e" using e_mem success by blast
  qed
qed

(* それぞれの同値パーティションから任意の代表値を1つずつ選び、そのいずれかの代表値のテストが失敗すれば完成正当性は成立しない。*)
lemma iff_not_totallyCorrect:
  assumes ecp: "ecp spec ess"
      and possibleImpl: "prog \<in> possibleImpl spec"
  shows "(\<exists>es \<in> ess. \<exists>e \<in> es. \<not>test spec prog e) \<longleftrightarrow> \<not>totallyCorrect spec prog"
proof (auto simp add: totallyCorrect_iff)
  fix e
  assume fail: "\<not> test spec prog e"
  hence precond: "precond spec e" unfolding test_def by simp
  then obtain es where e_mem: "e \<in> es" and es_mem: "es \<in> ess" using ecp_UnD[OF ecp] by blast
  thus "\<exists>es \<in> ess. \<exists>e \<in> es. \<not> test spec prog e" using fail by blast
qed

definition complete :: "spec \<Rightarrow> env set \<Rightarrow> bool"
  where "complete spec es \<equiv> \<exists>ess. ecp spec ess \<and> es \<in> representatives ess"

definition successful :: "spec \<Rightarrow> prog \<Rightarrow> env set \<Rightarrow> bool"
  where "successful spec prog es \<equiv> \<forall>e \<in> es. test spec prog e"

lemma successful_iff:
  assumes ecp: "ecp spec ess"
      and possibleImpl: "prog \<in> possibleImpl spec"
      and es_mem: "es \<in> representatives ess"
  shows "successful spec prog es \<longleftrightarrow> totallyCorrect spec prog"
proof
  assume successful: "successful spec prog es"
  have "\<And>es. es \<in> ess \<Longrightarrow> \<exists>e \<in> es. test spec prog e" using representatives_exI[OF ecp_partitionsD[OF ecp], OF es_mem, where ?P="test spec prog"] successful unfolding successful_def by blast
  thus "totallyCorrect spec prog" unfolding iff_totallyCorrect[OF ecp, OF possibleImpl, symmetric] by simp
next
  assume totallyCorrect: "totallyCorrect spec prog"
  thus "successful spec prog es" unfolding successful_def totallyCorrect_iff by simp
qed

definition reliable :: "spec \<Rightarrow> prog \<Rightarrow> bool"
  where "reliable spec prog \<equiv> \<forall>es1 \<subseteq> Collect (precond spec). \<forall>es2 \<subseteq> Collect (precond spec). complete spec es1 \<and> complete spec es2 \<longrightarrow> (successful spec prog es1 \<longleftrightarrow> successful spec prog es2)"

lemma reliable:
  assumes possibleImpl: "prog \<in> possibleImpl spec"
  shows "reliable spec prog"
unfolding reliable_def proof clarify
  fix es1 es2
  assume complete1: "complete spec es1"
    and complete2: "complete spec es2"
  obtain ess1 where ecp1: "ecp spec ess1" and representatives1: "es1 \<in> representatives ess1" using complete1 unfolding complete_def by blast
  obtain ess2 where ecp2: "ecp spec ess2" and representatives2: "es2 \<in> representatives ess2" using complete2 unfolding complete_def by blast
  show "successful spec prog es1 = successful spec prog es2" unfolding successful_iff[OF ecp1, OF possibleImpl, OF representatives1] successful_iff[OF ecp2, OF possibleImpl, OF representatives2] by (rule refl)
qed

definition valid :: "spec \<Rightarrow> prog \<Rightarrow> bool"
  where "valid spec prog \<equiv> \<forall>e. (precond spec e \<and> \<not>test spec prog e) \<longrightarrow> (\<exists>es. complete spec es \<and> \<not>successful spec prog es)"

lemma valid:
  assumes possibleImpl: "prog \<in> possibleImpl spec"
  shows "valid spec prog"
unfolding valid_def proof auto
  fix e
  assume precond: "precond spec e"
     and not_ok: "\<not> test spec prog e"
  have precond_nempty: "Collect (precond spec) \<noteq> {}" using precond by blast
  show "\<exists>es. complete spec es \<and> \<not>successful spec prog es" proof (rule exI[where ?x="Collect (precond spec)"], auto)
    show "complete spec (Collect (precond spec))" unfolding complete_def proof (rule exI[where ?x="singletons (Collect (precond spec))"], auto)
      show "ecp spec (singletons (Collect (precond spec)))" using precond_nempty by (rule ecp_singletons)
    next
      show "Collect (precond spec) \<in> representatives (singletons (Collect (precond spec)))" unfolding representatives_singletons[OF precond_nempty] by simp
    qed
  next
    assume "successful spec prog (Collect (precond spec))"
    thus False unfolding successful_def using not_ok precond by simp
  qed
qed


end