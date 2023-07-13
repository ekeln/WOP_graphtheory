theory WOP_koenig
imports Main
begin

type_synonym 'a Edge = "'a \<times> 'a"

record 'a Graph =
  verts :: "'a set" ("V\<index>")
  arcs :: "'a Edge set" ("E\<index>")
abbreviation is_arc :: "('a, 'b) Graph_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<rightarrow>\<index>" 60) where
  "v \<rightarrow>\<^bsub>G\<^esub> w \<equiv> (v,w) \<in> E\<^bsub>G\<^esub>"

locale Graph =
  fixes G :: "('a, 'b) Graph_scheme" (structure)
  assumes finite_vertex_set: "finite V"
    and valid_edge_set: "E \<subseteq> V \<times> V"
    and undirected: "v\<rightarrow>w = w\<rightarrow>v"
    and bipartit: "\<exists>A B.(A \<union> B = V) \<and> (\<forall>a \<in> A. (\<not>(\<exists>b \<in> A. ((a, b) \<in> E )))) \<and> 
      (\<forall>a \<in> B. (\<not>(\<exists>b \<in> B. ((a, b) \<in> E )))) \<and> (\<forall>v \<in> V. \<not>(v \<in> A \<and> v \<in> B))"
begin

fun neighbors :: "'a \<Rightarrow> 'a set" where
"neighbors v = {w . (v, w) \<in> E}"

fun degree :: "'a \<Rightarrow> nat" where
"degree v = (if neighbors v = {} then 0 else card (neighbors v))"

(* Für leeren Graph sei max_deg = 0*)
definition max_degree :: "nat" where
"max_degree = (if (V = {}) then 0 else Max {degree v| v. v \<in> V})"

(*TODO*)
lemma max_deg_k: "(max_degree = k) = (if (V = {}) then (k = 0) else (\<not>(\<exists>w \<in> V. degree w > k) \<and> (\<exists>u \<in> V. degree u = k)))"
  sorry
proof(simp)
  assume A1: "(max_degree = k)"
  then have "(if (V = {}) then 0 else Max {degree v| v. v \<in> V}) = k" by (unfold max_degree_def)
  then have A2: "(V = {} \<longrightarrow> k=0)  \<and> (V\<noteq>{} \<longrightarrow> Max {degree v| v. v \<in> V} = k)"
  by presburger
  show "(V = {} \<longrightarrow> k = 0) \<and>
    (V \<noteq> {} \<longrightarrow>
     (\<forall>w\<in>V. (\<exists>x. w \<rightarrow> x) \<longrightarrow> \<not> k < card {wa. w \<rightarrow> wa}) \<and>
     (\<exists>u\<in>V. ((\<forall>x. (u, x) \<notin> E) \<longrightarrow> k = 0) \<and> ((\<exists>x. u \<rightarrow> x) \<longrightarrow> card {w. u \<rightarrow> w} = k)))"
  proof(rule conjI)
    show "V = {} \<longrightarrow> k = 0"
    proof(rule impI)
      assume A3: "V = {}"
      from this A2 show " k = 0" by simp
    qed
  next
    show " V \<noteq> {} \<longrightarrow>
    (\<forall>w\<in>V. (\<exists>x. w \<rightarrow> x) \<longrightarrow> \<not> k < card {wa. w \<rightarrow> wa}) \<and>
    (\<exists>u\<in>V. ((\<forall>x. (u, x) \<notin> E) \<longrightarrow> k = 0) \<and> ((\<exists>x. u \<rightarrow> x) \<longrightarrow> card {w. u \<rightarrow> w} = k))"
    proof(rule impI)
      assume A4:"V \<noteq> {}"
      show "(\<forall>w\<in>V. (\<exists>x. w \<rightarrow> x) \<longrightarrow> \<not> k < card {wa. w \<rightarrow> wa}) \<and>
    (\<exists>u\<in>V. ((\<forall>x. (u, x) \<notin> E) \<longrightarrow> k = 0) \<and> ((\<exists>x. u \<rightarrow> x) \<longrightarrow> card {w. u \<rightarrow> w} = k))"
      proof(rule conjI)
        from A4 A2 have "(Max {degree v| v. v \<in> V} = k)" by simp
        then have "(Max{(if neighbors v = {} then 0 else card (neighbors v))|v. v\<in> V}) = k" by simp
        oops

(*leerer Graph sei 0 regulär*)
definition k_reg :: "nat \<Rightarrow> bool" where
"k_reg (k::nat) \<equiv> (if (V = {}) then (k=0) else  (\<forall>v \<in> V. (degree v) = k))"

(*Perfektes Matching:
A ist ein perfektes Matching wenn jeder Knoten von A abgedeckt ist aber nur einmal getroffen wird.*)
definition perf_match :: "'a Edge set \<Rightarrow> bool" where
"perf_match A \<equiv> (\<forall>v \<in> V.\<exists>e \<in> A. \<exists>w \<in> V. e = (v, w) \<and> (\<forall>f \<in> A. (e = f) \<or> \<not>(\<exists>u \<in> V. f = (v, u))))"

definition perf_match_alt :: "'a Edge set \<Rightarrow> bool" where
"perf_match_alt A \<equiv> (\<forall>v \<in> V.\<exists>e \<in> A. \<exists>w \<in> V. e = (v, w) \<and> (\<forall>u \<in> V. (u=w \<or> \<not>((v, u)\<in>A))))"

definition perf_match_alt2 :: "'a Edge set \<Rightarrow> bool" where
"perf_match_alt2 A \<equiv> (\<forall>v \<in> V. \<exists>w \<in>V. (v, w) \<in> A \<and> (\<forall>u \<in> V. u = w \<or> \<not>((v, u) \<in> A)))"

lemma "perf_match_alt A = perf_match A"
  by (smt (verit) Graph.perf_match_def Graph_axioms perf_match_alt_def prod.inject)

lemma "perf_match A = perf_match_alt2 A"
  by (smt (verit, del_insts) Pair_inject perf_match_alt2_def perf_match_def)


(* Für k=0: Wenn E \<noteq> {} dann ist A={} keine Zerlegung, aber im Kontext k-regulär reicht das.*)
definition perf_match_zerlegung :: "'a Edge set set \<Rightarrow> nat \<Rightarrow> bool" where
"perf_match_zerlegung A k \<equiv> (if k=0 then A={} 
else (card A = k \<and> (\<forall>a \<in> E. \<exists>B \<in> A. a \<in> B) \<and> (\<forall>B \<in> A. (\<forall>a \<in> B. \<not>(\<exists>B2 \<in> A. B2 \<noteq> B \<and> a \<in> B2)))))"

(*Kantenmenge sodass keine zwei Kanten zu dem gleichen Knoten inzident sind.*)
(*matching*)
definition class2 :: "('a Edge set) \<Rightarrow> bool" where
"class2 A \<equiv> (\<forall>(v, w) \<in> A. (v, w) \<in> E \<and> \<not>(\<exists>e \<in> A. (v, w) \<noteq> e \<and> (\<exists>u \<in> V. e = (v, u))))"

(*Menge A besteht aus k Mengen, die alle class2-Mengen sind also die keine zwei Kanten mit gleichem inzidenten Knoten enthalten.
Alle Kanten sind in einer der Mengen.*)
definition is_k_class_decompos ::"('a Edge set) set \<Rightarrow> nat \<Rightarrow> bool" where
"is_k_class_decompos A k \<equiv> (if k=0 then (A={} \<and> E={}) else 
(card A = k) \<and> (\<forall>B \<in> A. class2 B) \<and> (\<forall>e \<in> E. \<exists>B \<in> A. e \<in> B))"

(*Wenn Graph endlich, bipartit, max Grad k dann gibt es eine Zerlegung in k Klassen, 
sodass zwei Klassen mit inzidentem Knoten immer zu verschiedenen Klassen gehören.*)
lemma 15: 
  fixes k::nat
  assumes A1: "max_degree = k"
  shows "\<exists>A. is_k_class_decompos A k"
  sorry

(*TODO: Beweis
Wenn Graph endlich, bipartit und k regulär dann muss jeder Matching aus der Zerlegung aus Th. 15 genau
eine Kante zu jedem Knoten enthalten.
Beweisidee: Da sonst eine der anderen Klassen min. 2 Kanten zu einem Knoten haben müsste, was
keine korrekte Zerlegung mehr wäre.*)
lemma k_reg_theorem_15:
  fixes k::nat
  assumes A1: "k_reg k"
(*aufschlüsselung: Es gibt eine Zerlegung A. Für jede Zerlegung gilt, jedes Matching der Zerlegung
enthält für jeden Knoten genau eine inzidente Kante.*)
  shows "(\<exists>A. is_k_class_decompos A k) \<and> 
(\<forall>A. (is_k_class_decompos A k) \<longrightarrow> (\<forall>B \<in> A. \<forall>v \<in> V. (\<exists>w \<in> V. (v, w) \<in> B \<and> (\<forall>u \<in> V. u=w \<or> (v, u) \<notin> B))))"
  by (metis Graph.bipartit Graph_axioms UNIV_witness UnCI)


(*Definition von k reg, max deg prüfen, vereinfachen? *)
lemma k_reg_k_max: "k_reg k \<Longrightarrow> (max_degree = k)"
proof-
  assume A1: "k_reg k"
  show "(max_degree = k)"
  proof(unfold max_deg_k)
    show "if V = {} then k = 0 else \<not> (\<exists>w\<in>V. k < degree w) \<and> (\<exists>u\<in>V. degree u = k)"
    proof(simp)
      from A1 have A2: "(if (V = {}) then (k=0) else  (\<forall>v \<in> V. (degree v) = k))"
        by (unfold k_reg_def)
      have A3: "(if (V = {}) then (k=0) else  (\<forall>v \<in> V. (degree v) = k)) = 
        (((V = {}) \<longrightarrow> (k = 0)) \<and> ((V \<noteq> {}) \<longrightarrow> ((\<forall>v \<in> V. (degree v) = k))))" 
        by simp
      from A2 this have A4:"(V = {} \<longrightarrow> k = 0)" by simp
      from A2 this have A5: "((V \<noteq> {}) \<longrightarrow> ((\<forall>v \<in> V. (degree v) = k)))" by metis
      show "(V = {} \<longrightarrow> k = 0) \<and>
    (V \<noteq> {} \<longrightarrow>
     (\<forall>w\<in>V. (\<exists>x. w \<rightarrow> x) \<longrightarrow> \<not> k < card {wa. w \<rightarrow> wa}) \<and>
     (\<exists>u\<in>V. ((\<forall>x. (u, x) \<notin> E) \<longrightarrow> k = 0) \<and> ((\<exists>x. u \<rightarrow> x) \<longrightarrow> card {w. u \<rightarrow> w} = k)))"
      proof(rule conjI)
        from A4 show  "V = {} \<longrightarrow> k = 0" by assumption
      next
        show "V \<noteq> {} \<longrightarrow>
    (\<forall>w\<in>V. (\<exists>x. w \<rightarrow> x) \<longrightarrow> \<not> k < card {wa. w \<rightarrow> wa}) \<and>
    (\<exists>u\<in>V. ((\<forall>x. (u, x) \<notin> E) \<longrightarrow> k = 0) \<and> ((\<exists>x. u \<rightarrow> x) \<longrightarrow> card {w. u \<rightarrow> w} = k))"
        proof(rule impI)
          assume A6: "V \<noteq> {}"
          from A6 A5 have A7: "(\<forall>v \<in> V. (degree v) = k)"
          using A5 by fastforce
          then have A9: "(\<forall>v \<in> V. card (neighbors v) = k)"
            by auto
          then have A10: "(\<forall>v \<in> V. card ({w . (v, w) \<in> E}) = k)" 
            by (unfold local.neighbors.simps)
          show "(\<forall>w\<in>V. (\<exists>x. w \<rightarrow> x) \<longrightarrow> \<not> k < card {wa. w \<rightarrow> wa}) \<and>
    (\<exists>u\<in>V. ((\<forall>x. (u, x) \<notin> E) \<longrightarrow> k = 0) \<and> ((\<exists>x. u \<rightarrow> x) \<longrightarrow> card {w. u \<rightarrow> w} = k))"
          proof(rule conjI)
            from A9 show "\<forall>w\<in>V. (\<exists>x. w \<rightarrow> x) \<longrightarrow> \<not> k < card {wa. w \<rightarrow> wa}" by simp
          next
            from A6 A9 show "\<exists>u\<in>V. ((\<forall>x. (u, x) \<notin> E) \<longrightarrow> k = 0) \<and> ((\<exists>x. u \<rightarrow> x) \<longrightarrow> card {w. u \<rightarrow> w} = k)"
              by auto
          qed
        qed
      qed
    qed
  qed
qed

lemma perf_match_2:
  fixes A::"'a Edge set"
  shows "(\<forall>v \<in> V. (\<exists>w \<in> V. (v, w) \<in> A \<and> (\<forall>u \<in> V. u=w \<or> (v, u) \<notin> A))) \<Longrightarrow> perf_match A"
proof-
  assume A1: "(\<forall>v \<in> V. (\<exists>w \<in> V. (v, w) \<in> A \<and> (\<forall>u \<in> V. u=w \<or> (v, u) \<notin> A)))"
  show "perf_match A"
  proof(unfold perf_match_def)
    show "\<forall>v\<in>V. \<exists>e\<in>A. \<exists>w\<in>V. e = (v, w) \<and> (\<forall>f\<in>A. e = f \<or> \<not> (\<exists>u\<in>V. f = (v, u)))"
    proof(rule ballI)
      fix v
      assume A2: "v \<in> V"
      from A1 this have A3: "(\<exists>w \<in> V. (v, w) \<in> A \<and> (\<forall>u \<in> V. u=w \<or> (v, u) \<notin> A))" 
        by (rule bspec)
      then obtain w1 where A4: "(v, w1) \<in> A \<and> (\<forall>u \<in> V. u=w1 \<or> (v, u) \<notin> A)" 
        by (rule bexE)
      then have A5: "(v, w1) \<in> A " by (rule conjE)
      from A4 have A6: "(\<forall>u \<in> V. u=w1 \<or> (v, u) \<notin> A)" by (rule conjE)
          (*Sledgehammering*)
      from A5 have A7: "w1 \<in> V"
        using A3 A4 by fastforce
      show "\<exists>e\<in>A. \<exists>w\<in>V. e = (v, w) \<and> (\<forall>f\<in>A. e = f \<or> \<not> (\<exists>u\<in>V. f = (v, u)))"
      proof(rule bexI)
        show "\<exists>w\<in>V. (v, w1) = (v, w) \<and> (\<forall>f\<in>A. (v, w1) = f \<or> \<not> (\<exists>u\<in>V. f = (v, u)))"
        proof(rule bexI)
          show "(v, w1) = (v, w1) \<and> (\<forall>f\<in>A. (v, w1) = f \<or> \<not> (\<exists>u\<in>V. f = (v, u)))"
          proof(rule conjI)
            show "(v, w1) = (v, w1)" by simp
          next
            show "\<forall>f\<in>A. (v, w1) = f \<or> \<not> (\<exists>u\<in>V. f = (v, u))" 
            proof(rule ballI)
              fix f
              assume A8: "f \<in> A"
              have A9: "(v, w1) = f \<or> (v, w1) \<noteq> f" by simp
              then show "(v, w1) = f \<or> \<not> (\<exists>u\<in>V. f = (v, u))"
              proof(rule disjE)
                assume "(v, w1) = f" 
                then show "(v, w1) = f \<or> \<not> (\<exists>u\<in>V. f = (v, u))" by simp
              next
                assume A10: "(v, w1) \<noteq> f"
                show "(v, w1) = f \<or> \<not> (\<exists>u\<in>V. f = (v, u))"
                proof(rule disjI2)
                  show "\<not> (\<exists>u\<in>V. f = (v, u))"
                  proof(unfold bex_simps)
                    show " \<forall>x\<in>V. f \<noteq> (v, x)"
                    proof(rule ballI)
                      fix x
                      assume "x \<in> V"
                      show "f \<noteq> (v, x)"
                        using A10 A4 A8 \<open>x \<in> V\<close> by fastforce
                    qed
                  qed
                qed
              qed
            qed
          qed
          from A7 show "w1 \<in> V" by assumption
        qed
        from A5 show "(v, w1) \<in> A " by assumption
      qed
    qed
  qed
qed

lemma perf_matching_empty:
"V = {} \<Longrightarrow> perf_match {}"
  using perf_match_def by auto

lemma 14[simp]:
  fixes k ::nat
  assumes A1: "(k_reg k)"
(*B: Mengen an prfekten Matchings
A, A2: einzelne perfekte Matchings
a: Kanten in den Matchings (A, A2)*)
(*Aussage aufgeschlüsselt: Es gibt eine Zerlegung B, sodass B aus k perfekten Matchings besteht und diese
Matchings paarweise disjunkt sind. *)
  shows "\<exists>B. ((k=0 \<longrightarrow> B = {}) \<and> 
(\<not>(k=0) \<longrightarrow> (B = {A. (perf_match A)} \<and> (\<forall>a \<in> E. \<exists>A \<in> B. a \<in> A) \<and> card B = k)))"
proof-
from A1 have A2: "max_degree = k" by (rule k_reg_k_max)
  then have A3: "\<exists>C. is_k_class_decompos C k" by (rule 15)
  then obtain C where A4: "is_k_class_decompos C k" by (rule exE)
  from k_reg_theorem_15 A1 A4 have A5: "(\<forall>B \<in> C. \<forall>v \<in> V. (\<exists>w \<in> V. (v, w) \<in> B \<and> (\<forall>u \<in> V. u=w \<or> (v, u) \<notin> B)))"
    by simp
      (*Sledgehammered*)
  have A6: "card C = k" using A4 is_k_class_decompos_def
    by (metis card.empty)
  show "\<exists>B. (k = 0 \<longrightarrow> B = {}) \<and> 
(k \<noteq> 0 \<longrightarrow> B = Collect perf_match \<and>  (\<forall>a \<in> E. \<exists>A \<in> B. a \<in> A)\<and> card B = k)"
  proof(rule exI)
    have "k \<noteq> 0 \<longrightarrow> C = {A. (perf_match A)}" 
      by (metis A2 Un_empty bipartit max_degree_def)
    show "(k = 0 \<longrightarrow> C = {}) \<and> 
(k \<noteq> 0 \<longrightarrow> C = Collect perf_match \<and> (\<forall>a \<in> E. \<exists>A \<in> C. a \<in> A) \<and> card C = k)"
    proof(rule conjI)
      show "k = 0 \<longrightarrow> C = {}"
      proof(rule impI)
        assume A8: "k = 0"
        show "C = {}"
        proof-
          from A4 have "(if k=0 then C={} else 
(card C = k) \<and> (\<forall>B \<in> C. class2 B) \<and> (\<forall>e \<in> E. \<exists>B \<in> C. e \<in> B))"
            by (simp add: Graph.is_k_class_decompos_def Graph_axioms)
          then have "k=0 \<longrightarrow> C={}" by simp
          from this A8 show "C={}" by simp
        qed
      qed
    next
      show " k \<noteq> 0 \<longrightarrow> C = Collect perf_match \<and> (\<forall>a\<in>E. \<exists>A\<in>C. a \<in> A) \<and> card C = k "
      proof(rule impI)
        assume "k \<noteq> 0"
        show "C = Collect perf_match \<and> (\<forall>a\<in>E. \<exists>A\<in>C. a \<in> A) \<and> card C = k"
          using A4 \<open>k \<noteq> 0 \<longrightarrow> C = Collect perf_match\<close> \<open>k \<noteq> 0\<close> is_k_class_decompos_def by auto
      qed
    qed
  qed
qed

lemma koenig:
  fixes k::nat
  assumes A1: "k_reg k"
  shows "\<exists>A. perf_match_zerlegung A k"
proof-
  from A1 have A2: "max_degree = k" by (rule k_reg_k_max)
  then have A3: "\<exists>C. is_k_class_decompos C k" by (rule 15)
  then obtain C where A4: "is_k_class_decompos C k" by (rule exE)
  from k_reg_theorem_15 A1 A4 have A5: "(\<forall>B \<in> C. \<forall>v \<in> V. (\<exists>w \<in> V. (v, w) \<in> B \<and> (\<forall>u \<in> V. u=w \<or> (v, u) \<notin> B)))"
    by simp
  from A4 have A6: "(if k=0 then (C={} \<and> E={}) else 
(card C = k) \<and> (\<forall>B \<in> C. class2 B) \<and> (\<forall>e \<in> E. \<exists>B \<in> C. e \<in> B))" by (unfold is_k_class_decompos_def)
  then have A7: "k=0 \<longrightarrow> C ={} \<and> k > 0 \<longrightarrow> (card C = k) \<and> (\<forall>B \<in> C. class2 B) \<and> (\<forall>e \<in> E. \<exists>B \<in> C. e \<in> B)"
    by simp
  show "\<exists>A. perf_match_zerlegung A k"
  proof(rule exI)
    show "perf_match_zerlegung C k"
    proof(unfold perf_match_zerlegung_def)
      show "if k = 0 then C = {} else card C = k \<and> (\<forall>a\<in>E. \<exists>B\<in>C. a \<in> B) \<and> (\<forall>B\<in>C. \<forall>a\<in>B. \<not> (\<exists>B2\<in>C. B2 \<noteq> B \<and> a \<in> B2))"
      proof(simp)
        show "(k = 0 \<longrightarrow> C = {}) \<and> (0 < k \<longrightarrow> card C = k \<and> (\<forall>a\<in>E. \<exists>B\<in>C. a \<in> B) \<and> (\<forall>B\<in>C. \<forall>a\<in>B. \<forall>B2\<in>C. B2 = B \<or> a \<notin> B2))"
        proof(rule conjI)
          show "k = 0 \<longrightarrow> C = {}"
          proof(rule impI)
            assume A8: "k = 0"
            from this A6 show "C = {}" by simp
          qed
        next
          show "0 < k \<longrightarrow> card C = k \<and> (\<forall>a\<in>E. \<exists>B\<in>C. a \<in> B) \<and> (\<forall>B\<in>C. \<forall>a\<in>B. \<forall>B2\<in>C. B2 = B \<or> a \<notin> B2)"
          proof(rule impI)
            assume A8: "0 < k"
            show "card C = k \<and> (\<forall>a\<in>E. \<exists>B\<in>C. a \<in> B) \<and> (\<forall>B\<in>C. \<forall>a\<in>B. \<forall>B2\<in>C. B2 = B \<or> a \<notin> B2)"
            proof(rule conjI)
              from A8 A6 show "card C = k" by simp
            next
              show "(\<forall>a\<in>E. \<exists>B\<in>C. a \<in> B) \<and> (\<forall>B\<in>C. \<forall>a\<in>B. \<forall>B2\<in>C. B2 = B \<or> a \<notin> B2)"
              proof(rule conjI)
                from A8 A7 have A9: "(\<forall>B \<in> C. class2 B)"
                  using A6 by presburger
                from A6 A8 have A10: "(\<forall>e \<in> E. \<exists>B \<in> C. e \<in> B)" by simp
                show "\<forall>a\<in>E. \<exists>B\<in>C. a \<in> B"
                proof(rule ballI)
                  fix a
                  assume A11:"a\<in>E"
                  from A10 A11 show "\<exists>B\<in>C. a \<in> B" by (rule bspec)
                qed
              next
                show "(\<forall>B\<in>C. \<forall>a\<in>B. \<forall>B2\<in>C. B2 = B \<or> a \<notin> B2)"
                proof(rule ballI)
                  fix B
                  assume A12: "B \<in> C"
                  show "\<forall>a\<in>B. \<forall>B2\<in>C. B2 = B \<or> a \<notin> B2"
                  proof(rule ballI)
                    fix a
                    assume A13: "a \<in> B"
                    show " \<forall>B2\<in>C. B2 = B \<or> a \<notin> B2"
                    proof(rule ballI)
                      fix B2
                      assume A14: "B2 \<in> C"
                      have A15: "B2 = B \<or> B2 \<noteq> B" by simp
                      then show "B2 = B \<or> a \<notin> B2"
                      proof(rule disjE)
                        assume "B2=B" then show "B2 = B \<or> a \<notin> B2" by simp
                      next
                        assume A16: "B2 \<noteq> B"
                        show "B2 = B \<or> a \<notin> B2"
                        proof(rule disjI2) oops
                          
end
end