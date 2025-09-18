theory SubsetSum_DTM_Bridge
  imports "SubsetSum_DecisionTree"
begin

section \<open>DTM bridge: abstract run model\<close>

fun tm_to_dtr' ::
  "('C \<Rightarrow> int) \<Rightarrow> ('C \<Rightarrow> bool \<Rightarrow> 'C) \<Rightarrow> ('C \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'C \<Rightarrow> (nat,nat) dtr"
where
  "tm_to_dtr' head0 stepf final_acc 0 c = Leaf (final_acc c)"
| "tm_to_dtr' head0 stepf final_acc (Suc t) c =
     AskL (nat (head0 c))
          (tm_to_dtr' head0 stepf final_acc t (stepf c False))
          (tm_to_dtr' head0 stepf final_acc t (stepf c True))"

locale DTM_Run =
  fixes steps   :: "'M \<Rightarrow> bool list \<Rightarrow> nat"          (* halting time on input x *)
    and conf    :: "'M \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> 'C"     (* configuration after t steps *)
    and head0   :: "'C \<Rightarrow> int"                      (* position of input-tape head *)
    and accepts :: "'M \<Rightarrow> bool list \<Rightarrow> bool"         (* acceptance predicate *)
begin

definition read0 :: "'M \<Rightarrow> bool list \<Rightarrow> nat set" where
  "read0 M x = (\<lambda>t. nat (head0 (conf M x t))) ` {..< steps M x}"

lemma finite_read0[simp]: "finite (read0 M x)"
  unfolding read0_def by (intro finite_imageI) simp

lemma card_read0_le_steps:
  "card (read0 M x) \<le> steps M x"
  unfolding read0_def by (metis card_image_le card_lessThan finite_lessThan)

end

section \<open>Contiguous overwrite (splice)\<close>

definition splice :: "nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list" where
  "splice a w xs bs = take a xs @ bs @ drop (a + w) xs"

lemma splice_nth_inside:
  assumes LEN: "length bs = w"
      and BND: "a + w \<le> length xs"
      and IN1: "a \<le> i"
      and IN2: "i < a + w"
  shows "splice a w xs bs ! i = bs ! (i - a)"
proof -
  have ia_lt: "i - a < w" using IN1 IN2 by arith
  have a_le_len: "a \<le> length xs" using BND by linarith
  have "splice a w xs bs ! i = (take a xs @ bs @ drop (a + w) xs) ! i"
    by (simp add: splice_def)
  also have "... = (bs @ drop (a + w) xs) ! (i - a)"
    using IN1 a_le_len by (simp add: nth_append)
  also have "... = bs ! (i - a)"
    using ia_lt LEN by (simp add: nth_append)
  finally show ?thesis .
qed

lemma splice_nth_left:
  assumes BND: "a \<le> length xs"
      and L:   "i < a"
  shows "splice a w xs bs ! i = xs ! i"
  using assms by (simp add: splice_def nth_append)

lemma splice_nth_right:
  assumes LEN: "length bs = w"
      and BND: "a + w \<le> length xs"
      and R:   "a + w \<le> i"
  shows "splice a w xs bs ! i = xs ! i"
proof -
  have a_le_len: "a \<le> length xs" using BND by linarith
  have i_ge_a:   "a \<le> i"         using R   by linarith
  have i_minus_ge_w: "i - a \<ge> w" using R   by arith
  have "splice a w xs bs ! i = (take a xs @ bs @ drop (a + w) xs) ! i"
    by (simp add: splice_def)
  also have "... = (bs @ drop (a + w) xs) ! (i - a)"
    using i_ge_a a_le_len by (simp add: nth_append)
  also have "... = drop (a + w) xs ! (i - a - length bs)"
    using LEN i_minus_ge_w by (simp add: nth_append)
  also have "... = drop (a + w) xs ! (i - (a + w))"
    by (simp add: LEN)
  also have "... = xs ! i"
    using BND R by (simp add: add_diff_inverse_nat)
  finally show ?thesis .
qed

section \<open>DTM semantics sufficient for unread-agreement\<close>

locale DTM_Run_Sem =
  fixes steps     :: "'M \<Rightarrow> bool list \<Rightarrow> nat"
    and conf      :: "'M \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> 'C"
    and head0     :: "'C \<Rightarrow> int"
    and accepts   :: "'M \<Rightarrow> bool list \<Rightarrow> bool"
    and M         :: 'M
    and stepf     :: "'C \<Rightarrow> bool \<Rightarrow> 'C"
    and final_acc :: "'C \<Rightarrow> bool"
  assumes step_sem:
    "\<And>x t. conf M x (Suc t) = stepf (conf M x t) (x ! nat (head0 (conf M x t)))"
  assumes steps_stable_raw:
    "\<And>x y. (\<And>i. i \<in> ((\<lambda>t. nat (head0 (conf M x t))) ` {..< steps M x}) \<Longrightarrow> x ! i = y ! i)
           \<Longrightarrow> steps M x = steps M y"
  assumes accepts_sem:
    "\<And>x. accepts M x = final_acc (conf M x (steps M x))"
  assumes conf0_same: "\<And>x y. conf M x 0 = conf M y 0"
begin

primrec drive :: "nat \<Rightarrow> 'C \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'C" where
  "drive 0 c inp = c"
| "drive (Suc t) c inp =
     (let i = nat (head0 c); b = inp i in drive t (stepf c b) inp)"

lemma drive_conf_gen:
  "drive t (conf M x u) (\<lambda>i. x ! i) = conf M x (u + t)"
proof (induction t arbitrary: u)
  case 0 show ?case by simp
next
  case (Suc t)
  have "drive (Suc t) (conf M x u) (\<lambda>i. x ! i)
        = drive t (stepf (conf M x u) (x ! nat (head0 (conf M x u)))) (\<lambda>i. x ! i)"
    by simp
  also have "... = drive t (conf M x (Suc u)) (\<lambda>i. x ! i)"
    by (simp add: step_sem)
  also have "... = conf M x (Suc u + t)"
    by (simp add: Suc.IH)
  finally show ?case by simp
qed

lemma drive_conf:
  "drive t (conf M x 0) (\<lambda>i. x ! i) = conf M x t"
  by (simp add: drive_conf_gen)

(* Decision tree eval matches the driven TM evolution *)
lemma run_tm_to_dtr':
  "run oL oR (tm_to_dtr' head0 stepf final_acc t c)
   = final_acc (drive t c oL)"
  by (induction t arbitrary: c) (simp_all add: Let_def)

(* Specialize to x and steps M x *)
lemma tm_to_dtr_correct:
  "run (\<lambda>i. x ! i) (\<lambda>i. x ! i)
        (tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0))
   = final_acc (conf M x (steps M x))"
  by (simp add: run_tm_to_dtr' drive_conf)

corollary tm_to_dtr_accepts:
  "run (\<lambda>i. x ! i) (\<lambda>i. x ! i)
        (tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0))
   = accepts M x"
  by (simp add: tm_to_dtr_correct accepts_sem)

(* local read-set, if you need it later *)
definition read0S :: "bool list \<Rightarrow> nat set" where
  "read0S x = (\<lambda>t. nat (head0 (conf M x t))) ` {..< steps M x}"

(* handy: one-step shift for images over {..<t} to {..<Suc t} *)
lemma image_shift_suc_subset:
  fixes F :: "nat \<Rightarrow> 'a"
  shows "(\<lambda>u. F u) ` {..<t} \<subseteq> F ` {..<Suc t}"
  by auto

lemma seenL_tm_to_dtr_subset_read0_helper:
  "seenL_run oL oR (tm_to_dtr' head0 stepf final_acc t c)
     \<subseteq> (\<lambda>u. nat (head0 (drive u c oL))) ` {..< t}"
proof (induction t arbitrary: c)
  case 0
  show ?case by simp
next
  case (Suc t)
  let ?i = "nat (head0 c)"

  have root_in:
    "?i \<in> (\<lambda>u. nat (head0 (drive u c oL))) ` {..< Suc t}"
    by (rule image_eqI[where x=0]) simp_all

  have IH_sub:
    "seenL_run oL oR
       (tm_to_dtr' head0 stepf final_acc t (stepf c (oL ?i)))
     \<subseteq> (\<lambda>u. nat (head0 (drive u (stepf c (oL ?i)) oL))) ` {..< t}"
    by (rule Suc.IH)

  have drive_suc:
    "(\<lambda>u. nat (head0 (drive u (stepf c (oL ?i)) oL)))
     = (\<lambda>u. nat (head0 (drive (Suc u) c oL)))"
    by (intro ext) simp

  have sub_into_parent:
    "(\<lambda>u. nat (head0 (drive (Suc u) c oL))) ` {..< t}
     \<subseteq> (\<lambda>u. nat (head0 (drive u c oL))) ` {..< Suc t}"
  proof
    fix y
    assume "y \<in> (\<lambda>u. nat (head0 (drive (Suc u) c oL))) ` {..< t}"
    then obtain u where u_lt: "u < t"
      and y_def: "y = nat (head0 (drive (Suc u) c oL))" by auto
    have "y = (\<lambda>v. nat (head0 (drive v c oL))) (Suc u)"
      by (simp add: y_def)
    moreover have "Suc u \<in> {..< Suc t}"
      using u_lt by simp
    ultimately show "y \<in> (\<lambda>u. nat (head0 (drive u c oL))) ` {..< Suc t}"
      by (rule image_eqI)
  qed

  have split:
    "seenL_run oL oR (tm_to_dtr' head0 stepf final_acc (Suc t) c)
       = insert ?i (seenL_run oL oR
              (tm_to_dtr' head0 stepf final_acc t (stepf c (oL ?i))))"
    by simp

  show ?case
    using root_in IH_sub split drive_suc sub_into_parent by auto
qed



sublocale Base: DTM_Run steps conf head0 accepts .

lemma seenL_tm_to_dtr_subset_read0:
  fixes x :: "bool list"
  defines "T \<equiv> tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0)"
  shows "seenL_run (\<lambda>i. x ! i) (\<lambda>j. x ! j) T \<subseteq> Base.read0 M x"
proof -
  have A:
    "seenL_run (\<lambda>i. x ! i) (\<lambda>j. x ! j)
       (tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0))
     \<subseteq> (\<lambda>u. nat (head0 (drive u (conf M x 0) (\<lambda>i. x ! i)))) ` {..< steps M x}"
    by (rule seenL_tm_to_dtr_subset_read0_helper)
  also have "\<dots> = (\<lambda>u. nat (head0 (conf M x u))) ` {..< steps M x}"
    by (simp add: drive_conf)
  also have "\<dots> = Base.read0 M x"
    unfolding Base.read0_def by simp
  finally show ?thesis by (simp add: T_def)
qed

(* 1) Helper proved by induction on t *)
lemma seenR_tm_to_dtr_subset_read0_helper:
  "seenR_run oL oR (tm_to_dtr' head0 stepf final_acc t c)
     \<subseteq> (\<lambda>u. nat (head0 (drive u c oL))) ` {..< t}"
proof (induction t arbitrary: c)
  case 0
  show ?case by simp
next
  case (Suc t)
  let ?i = "nat (head0 c)"
  have split:
    "seenR_run oL oR (tm_to_dtr' head0 stepf final_acc (Suc t) c)
     = seenR_run oL oR (tm_to_dtr' head0 stepf final_acc t (stepf c (oL ?i)))"
    by simp
  have IH_sub:
    "seenR_run oL oR (tm_to_dtr' head0 stepf final_acc t (stepf c (oL ?i)))
       \<subseteq> (\<lambda>u. nat (head0 (drive u (stepf c (oL ?i)) oL))) ` {..< t}"
    by (rule Suc.IH)
  have drive_suc:
    "(\<lambda>u. nat (head0 (drive u (stepf c (oL ?i)) oL)))
     = (\<lambda>u. nat (head0 (drive (Suc u) c oL)))"
    by (intro ext) simp
  have shift:
    "(\<lambda>u. nat (head0 (drive (Suc u) c oL))) ` {..< t}
       \<subseteq> (\<lambda>u. nat (head0 (drive u c oL))) ` {..< Suc t}"
  proof
    fix y assume "y \<in> (\<lambda>u. nat (head0 (drive (Suc u) c oL))) ` {..< t}"
    then obtain u where u:"u < t" and y:"y = nat (head0 (drive (Suc u) c oL))" by auto
    have "Suc u \<in> {..< Suc t}" using u by simp
    have mem: "Suc u \<in> {..< Suc t}" using u by simp
    have eq:  "y = (\<lambda>v. nat (head0 (drive v c oL))) (Suc u)" by (simp add: y)
    have "(\<lambda>v. nat (head0 (drive v c oL))) (Suc u)
        \<in> (\<lambda>v. nat (head0 (drive v c oL))) ` {..< Suc t}"
      using mem by (rule imageI)
    thus "y \<in> (\<lambda>v. nat (head0 (drive v c oL))) ` {..< Suc t}"
      by (simp add: eq)
  qed
  from split IH_sub drive_suc shift show ?case by auto
qed

(* 2) Use the helper to get the version w.r.t. Base.read0 *)
lemma seenR_tm_to_dtr_subset_read0:
  fixes x :: "bool list"
  defines "T \<equiv> tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0)"
  shows "seenR_run (\<lambda>i. x ! i) (\<lambda>j. x ! j) T \<subseteq> Base.read0 M x"
proof -
  have
    "seenR_run (\<lambda>i. x ! i) (\<lambda>j. x ! j)
       (tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0))
     \<subseteq> (\<lambda>u. nat (head0 (drive u (conf M x 0) (\<lambda>i. x ! i)))) ` {..< steps M x}"
    by (rule seenR_tm_to_dtr_subset_read0_helper)
  also have "\<dots> = (\<lambda>u. nat (head0 (conf M x u))) ` {..< steps M x}"
    by (simp add: drive_conf)
  also have "\<dots> = Base.read0 M x"
    unfolding Base.read0_def by simp
  finally show ?thesis by (simp add: T_def)
qed

(* Bridge fact: our local read0S equals the inherited read0. *)
lemma read0_bridge: "read0S x = Base.read0 M x"
  by (simp add: read0S_def Base.read0_def)

lemma steps_stable:
  assumes AG: "\<And>i. i \<in> Base.read0 M x \<Longrightarrow> x ! i = y ! i"
  shows "steps M x = steps M y"
proof (rule steps_stable_raw)
  fix i
  assume iIn: "i \<in> (\<lambda>t. nat (head0 (conf M x t))) ` {..< steps M x}"
  (* 1) Turn it into membership in the local read-set *)
  have iR0S: "i \<in> read0S x"
    using iIn by (simp add: read0S_def)
  (* 2) Bridge to the locale’s read-set *)
  have iBase: "i \<in> Base.read0 M x"
    using iR0S by (simp add: read0_bridge)
  (* 3) Apply the assumption *)
  show "x ! i = y ! i" by (rule AG[OF iBase])
qed

(* helper: if t < steps, the index read at time t is in read0S *)
lemma idx_in_read0S:
  assumes "t < steps M x"
  shows "nat (head0 (conf M x t)) \<in> read0S x"
  using assms
  unfolding read0S_def
  by (intro image_eqI[where x=t]) simp_all

lemma unread_agreement:
  assumes AG: "\<And>i. i \<in> Base.read0 M x \<Longrightarrow> x ! i = y ! i"
  shows "accepts M x \<longleftrightarrow> accepts M y"
proof -
  (* same halting time *)
  have steps_eq: "steps M x = steps M y"
    by (rule steps_stable[OF AG])

  (* convert agreement to the local read-set once *)
  have AGS: "\<And>i. i \<in> read0S x \<Longrightarrow> x ! i = y ! i"
  proof -
    fix i assume "i \<in> read0S x"
    hence "i \<in> Base.read0 M x" by (simp add: read0_bridge)
    thus "x ! i = y ! i" by (rule AG)
  qed

  (* configurations match up to the halting time *)
  have conf_eq: "\<And>t. t \<le> steps M x \<Longrightarrow> conf M x t = conf M y t"
  proof-
    fix t :: nat
    show "t \<le> steps M x \<Longrightarrow> conf M x t = conf M y t"
    proof (induction t)
      case 0
      show ?case by (simp add: conf0_same) 
    next
      case (Suc t)
  (* from Suc t \<le> steps \<dots> get the strict bound we actually need *)
      have t_lt: "t < steps M x" using Suc.prems by simp

  (* apply IH at t \<le> steps \<dots> *)
      have IH: "conf M x t = conf M y t" by (rule Suc.IH) (use Suc.prems in simp)

      let ?i = "nat (head0 (conf M x t))"

  (* the scanned index at time t is in the read-set *)
      have i_mem: "?i \<in> read0S x"
        unfolding read0S_def
        by (intro image_eqI[where x=t]) (use t_lt in simp_all)

  (* inputs agree on that index *)
      have scan_eq: "x ! ?i = y ! ?i" using AGS i_mem by blast

  (* one deterministic step using same scanned bit *)
      let ?i = "nat (head0 (conf M x t))"

(* rewrite the index using the IH on configurations *)
      have i_y: "?i = nat (head0 (conf M y t))"
        by (simp add: IH)

      have "conf M x (Suc t) = stepf (conf M x t) (x ! ?i)"
        by (simp add: step_sem)
      also have "... = stepf (conf M y t) (y ! ?i)"
        using IH scan_eq by simp
      also have "... = stepf (conf M y t) (y ! nat (head0 (conf M y t)))"
        by (simp add: i_y)
      also have "... = conf M y (Suc t)"
        by (simp only: step_sem[symmetric])
      finally show ?case .
    qed
  qed

  (* acceptance depends only on final configuration *)
  have "accepts M x = final_acc (conf M x (steps M x))" by (rule accepts_sem)
  also have "... = final_acc (conf M y (steps M y))" using conf_eq steps_eq by simp
  also have "... = accepts M y" by (rule accepts_sem[symmetric])
  finally show ?thesis .
qed

abbreviation sp :: "nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list" where
  "sp \<equiv> SubsetSum_DTM_Bridge.splice"

end

section \<open>Catalog blocks and padded encoding\<close>

text \<open>We serialize the sets of LHS/RHS values into non-overlapping bit-blocks.\<close>

definition enumL where
  "enumL as s k = sorted_list_of_set (LHS (e_k as s k) (length as))"

definition enumR where
  "enumR as s k = sorted_list_of_set (RHS (e_k as s k) (length as))"

lemma finite_LHS[simp]: "finite (LHS e n)"
  unfolding LHS_def by fastforce

lemma finite_RHS[simp]: "finite (RHS e n)"
  unfolding RHS_def by fastforce

lemma enumL_set[simp]:
  "set (enumL as s k) = LHS (e_k as s k) (length as)"
  by (simp add: enumL_def)

lemma enumR_set[simp]:
  "set (enumR as s k) = RHS (e_k as s k) (length as)"
  by (simp add: enumR_def)

text \<open>Fixed block width; later you can make it logarithmic in the values.\<close>
definition W :: "int list \<Rightarrow> int \<Rightarrow> nat" where
  "W as s = max 1 (length as)"

definition offL :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat" where
  "offL as s j = j * W as s"

definition offR :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "offR as s k j = length (enumL as s k) * W as s + j * W as s"

definition blockL :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat set" where
  "blockL as s j = { offL as s j ..< offL as s j + W as s }"

definition blockR :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "blockR as s k j = { offR as s k j ..< offR as s k j + W as s }"

definition blockL_abs ::
  "(int list \<Rightarrow> int \<Rightarrow> bool list) \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat set" where
  "blockL_abs E as s j =
     { length (E as s) + offL as s j ..<
       length (E as s) + offL as s j + W as s }"

definition blockR_abs ::
  "(int list \<Rightarrow> int \<Rightarrow> bool list) \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "blockR_abs E as s k j =
     { length (E as s) + offR as s k j ..<
       length (E as s) + offR as s k j + W as s }"

lemma blockL_abs_disjoint:
  assumes "j \<noteq> j'"
  shows   "blockL_abs E as s j \<inter> blockL_abs E as s j' = {}"
proof -
  let ?W = "W as s"
  let ?c = "length (E as s)"
  have "j < j' \<or> j' < j" using assms by arith
  then show ?thesis
  proof
    assume lt: "j < j'"
    have "(Suc j) * ?W \<le> j' * ?W"
      using lt by (intro mult_right_mono) simp_all
    hence "?c + j * ?W + ?W \<le> ?c + j' * ?W" by simp
    thus ?thesis by (auto simp: blockL_abs_def offL_def)
  next
    assume lt: "j' < j"
    have "(Suc j') * ?W \<le> j * ?W"
      using lt by (intro mult_right_mono) simp_all
    hence "?c + j' * ?W + ?W \<le> ?c + j * ?W" by simp
    thus ?thesis by (auto simp: blockL_abs_def offL_def)
  qed
qed

lemma blockR_abs_disjoint:
  assumes "j \<noteq> j'"
  shows   "blockR_abs E as s k j \<inter> blockR_abs E as s k j' = {}"
proof -
  let ?W = "W as s"
  let ?c = "length (E as s)"
  have "j < j' \<or> j' < j" using assms by arith
  then show ?thesis
  proof
    assume lt: "j < j'"
    have "(Suc j) * ?W \<le> j' * ?W"
      using lt by (intro mult_right_mono) simp_all
    hence "?c + offR as s k j + ?W \<le> ?c + offR as s k j'"
      by (simp add: offR_def add_mult_distrib2)
    thus ?thesis by (auto simp: blockR_abs_def)
  next
    assume lt: "j' < j"
    have "(Suc j') * ?W \<le> j * ?W"
      using lt by (intro mult_right_mono) simp_all
    hence "?c + offR as s k j' + ?W \<le> ?c + offR as s k j"
      by (simp add: offR_def add_mult_distrib2)
    thus ?thesis by (auto simp: blockR_abs_def)
  qed
qed

lemma blockL_abs_blockR_abs_disjoint:
  assumes jL: "j < length (enumL as s k)"
  shows   "blockL_abs E as s j \<inter> blockR_abs E as s k j' = {}"
proof -
  let ?W = "W as s"
  let ?c = "length (E as s)"
  have step:
    "?c + offL as s j + ?W \<le> ?c + offR as s k j'"
  proof -
    have "(Suc j) * ?W \<le> length (enumL as s k) * ?W"
      using jL by (intro mult_right_mono) simp_all
    hence "?c + (Suc j) * ?W \<le> ?c + length (enumL as s k) * ?W" by simp
    also have "\<dots> \<le> ?c + (length (enumL as s k) * ?W + j' * ?W)" by simp
    finally show ?thesis
      by (simp add: offL_def offR_def add_mult_distrib2)
  qed
  show ?thesis
    using step by (auto simp: blockL_abs_def blockR_abs_def)
qed

(* same width, consecutive half-open blocks are disjoint when indices differ *)
lemma blocks_disjoint_same_base:
  fixes W :: nat
  assumes "W > 0" and "j \<noteq> j'"
  shows "{j*W ..< j*W + W} \<inter> {j'*W ..< j'*W + W} = {}"
proof -
  have "j < j' \<or> j' < j" using assms(2) by arith
  then show ?thesis
  proof
    assume lt: "j < j'"
    have "(Suc j) * W \<le> j' * W"
      using lt assms(1) by (intro mult_right_mono) simp_all
    hence "j*W + W \<le> j'*W" by simp
    thus ?thesis by auto
  next
    assume lt: "j' < j"
    have "(Suc j') * W \<le> j * W"
      using lt assms(1) by (intro mult_right_mono) simp_all
    hence "j'*W + W \<le> j*W" by simp
    thus ?thesis by auto
  qed
qed

(* Disjointness results *)
lemma blockL_disjoint:
  assumes "j \<noteq> j'"
  shows   "blockL as s j \<inter> blockL as s j' = {}"
proof -
  have Wpos: "W as s > 0" by (simp add: W_def)
  have base:
    "{offL as s j ..< offL as s j + W as s}
     \<inter> {offL as s j' ..< offL as s j' + W as s} = {}"
    using blocks_disjoint_same_base[of "W as s" j j'] Wpos assms
    by (simp add: offL_def)
  show ?thesis using blockL_def base by simp
qed

lemma blockR_disjoint:
  assumes "j \<noteq> j'"
  shows "blockR as s k j \<inter> blockR as s k j' = {}"
proof -
  have "j < j' \<or> j' < j" using assms by arith
  then show ?thesis
  proof
    assume lt: "j < j'"
    have "(Suc j) * W as s \<le> j' * W as s"
      using lt by (intro mult_right_mono) simp_all
    hence "offR as s k j + W as s \<le> offR as s k j'"
      by (simp add: offR_def algebra_simps)   (* j*W + W = (Suc j)*W *)
    thus ?thesis by (auto simp: blockR_def)
  next
    assume lt: "j' < j"
    have "(Suc j') * W as s \<le> j * W as s"
      using lt by (intro mult_right_mono) simp_all
    hence "offR as s k j' + W as s \<le> offR as s k j"
      by (simp add: offR_def algebra_simps)
    thus ?thesis by (auto simp: blockR_def)
  qed
qed

lemma blockL_blockR_disjoint:
  assumes jL: "j < length (enumL as s k)"
  shows "blockL as s j \<inter> blockR as s k j' = {}"
proof -
  let ?W = "W as s"
  let ?base = "length (enumL as s k) * ?W"

  have Suc_le: "Suc j \<le> length (enumL as s k)" using jL by simp
  have topL: "offL as s j + ?W \<le> ?base"
  proof -
    have "offL as s j + ?W = (j + 1) * ?W"
      by (simp add: offL_def add_mult_distrib2)
    also have "... \<le> length (enumL as s k) * ?W"
      using Suc_le by (intro mult_right_mono) simp_all
    finally show ?thesis .
  qed

  have "blockL as s j \<subseteq> {..< ?base}"
  proof
    fix x assume xL: "x \<in> blockL as s j"
    have x_lt: "x < offL as s j + W as s"
      using xL by (simp add: blockL_def)
    have "x < length (enumL as s k) * W as s"
      using x_lt topL by (rule less_le_trans)
    thus "x \<in> {..< length (enumL as s k) * W as s}"
  by simp
  qed
  moreover
  have "blockR as s k j' \<subseteq> {?base ..< ?base + ?W + j' * ?W}"
    by (auto simp: blockR_def offR_def W_def)
  ultimately show ?thesis by fastforce
qed

section \<open>Padding encoder\<close>

locale SubsetSum_Padded_Enc =
  fixes enc0      :: "int list \<Rightarrow> int \<Rightarrow> bool list"     (* baseline CL encoding *)
    and to_bits   :: "nat \<Rightarrow> int \<Rightarrow> bool list"           (* fixed-width bits of an integer *)
    and from_bits :: "bool list \<Rightarrow> int"
  assumes bits_roundtrip:
    "\<And>as s k v. v \<in> set (enumL as s k) \<union> set (enumR as s k) \<Longrightarrow>
       length (to_bits (W as s) v) = W as s \<and> from_bits (to_bits (W as s) v) = v"
begin

definition padL where
  "padL as s k = concat (map (to_bits (W as s)) (enumL as s k))"

definition padR where
  "padR as s k = concat (map (to_bits (W as s)) (enumR as s k))"

definition enc where
  "enc as s k = enc0 as s @ padL as s k @ padR as s k"

(* Sum of a constant over any list *)
lemma sum_const_all_nat: "(\<Sum> _\<leftarrow> L. (c::nat)) = length L * c" for L c
  by (induction L) simp_all

(* helper: length rule on elements of enumL / enumR *)
lemma to_bits_len_on_enumL:
  assumes vL: "v \<in> set (enumL as s k)"
  shows   "length (to_bits (W as s) v) = W as s"
proof -
  have inU: "v \<in> set (enumL as s k) \<union> set (enumR as s k)"
    using vL by auto   (* or: by (rule UnI1) *)
  from bits_roundtrip[OF inU] show ?thesis by simp
qed

lemma to_bits_len_on_enumR:
  assumes vR: "v \<in> set (enumR as s k)"
  shows   "length (to_bits (W as s) v) = W as s"
proof -
  have inU: "v \<in> set (enumL as s k) \<union> set (enumR as s k)"
    using vR by auto   (* or: by (rule UnI2) *)
  from bits_roundtrip[OF inU] show ?thesis by simp
qed

(* pointwise constant-length maps over the enumerations *)
lemma map_len_to_bits_constL:
  "map (\<lambda>v. length (to_bits (W as s) v)) (enumL as s k)
   = map (\<lambda>_. W as s) (enumL as s k)"
  by (rule map_cong[OF refl]) (simp add: to_bits_len_on_enumL)

lemma map_len_to_bits_constR:
  "map (\<lambda>v. length (to_bits (W as s) v)) (enumR as s k)
   = map (\<lambda>_. W as s) (enumR as s k)"
  by (rule map_cong[OF refl]) (simp add: to_bits_len_on_enumR)

lemma length_padL:
  "length (padL as s k) = length (enumL as s k) * W as s"
proof -
  have "length (padL as s k)
        = sum_list (map (length \<circ> to_bits (W as s)) (enumL as s k))"
    by (simp add: padL_def length_concat)
  also have "... = sum_list (map (\<lambda>v. length (to_bits (W as s) v)) (enumL as s k))"
    by (simp add: comp_def)
  also have "... = sum_list (map (\<lambda>_. W as s) (enumL as s k))"
    by (simp add: map_len_to_bits_constL)
  also have "... = length (enumL as s k) * W as s"
    by (rule sum_const_all_nat)
  finally show ?thesis .
qed

lemma length_padR:
  "length (padR as s k) = length (enumR as s k) * W as s"
proof -
  have "length (padR as s k)
        = sum_list (map (length \<circ> to_bits (W as s)) (enumR as s k))"
    by (simp add: padR_def length_concat)
  also have "... = sum_list (map (\<lambda>v. length (to_bits (W as s) v)) (enumR as s k))"
    by (simp add: comp_def)
  also have "... = sum_list (map (\<lambda>_. W as s) (enumR as s k))"
    by (simp add: map_len_to_bits_constR)
  also have "... = length (enumR as s k) * W as s"
    by (rule sum_const_all_nat)
  finally show ?thesis .
qed

lemma length_enc:
  "length (enc as s k)
   = length (enc0 as s)
     + length (enumL as s k) * W as s
     + length (enumR as s k) * W as s"
proof -
  have "length (enc as s k)
        = length (enc0 as s) + length (padL as s k) + length (padR as s k)"
    by (simp add: enc_def)
  also have "... = length (enc0 as s)
                     + length (enumL as s k) * W as s
                     + length (enumR as s k) * W as s"
    by (simp add: length_padL length_padR)
  finally show ?thesis .
qed

end

section \<open>Coverage via unread-agreement\<close>

locale Coverage_TM =
  DTM_Run_Sem steps conf head0 accepts M stepf final_acc +
  SubsetSum_Padded_Enc enc0 to_bits from_bits
  for steps :: "'M \<Rightarrow> bool list \<Rightarrow> nat"
  and conf  :: "'M \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> 'C"
  and head0 :: "'C \<Rightarrow> int"
  and accepts :: "'M \<Rightarrow> bool list \<Rightarrow> bool"
  and M :: 'M
  and stepf :: "'C \<Rightarrow> bool \<Rightarrow> 'C"
  and final_acc :: "'C \<Rightarrow> bool"
  and enc0  :: "int list \<Rightarrow> int \<Rightarrow> bool list"
  and to_bits :: "nat \<Rightarrow> int \<Rightarrow> bool list"
  and from_bits :: "bool list \<Rightarrow> int"
  +
fixes kk :: nat

  assumes correctness:
    "accepts M (enc as s kk)
       \<longleftrightarrow> good as s (\<lambda>i. (enc as s kk) ! i) (\<lambda>j. (enc as s kk) ! j)"
  assumes reader_sound_L:
  "\<lbrakk> j < length (enumL as s kk); v \<in> set (enumL as s kk) \<rbrakk>
   \<Longrightarrow> accepts M (splice (length (enc0 as s) + offL as s j)
                        (W as s) (enc as s kk) (to_bits (W as s) v))
       \<longleftrightarrow> (\<exists>xs\<in>bitvec (length as). lhs_of as kk xs = v \<and>
                            rhs_of as kk s xs \<in> set (enumR as s kk))"
  assumes reader_sound_R:
    "\<lbrakk> j < length (enumR as s kk); u \<in> set (enumR as s kk) \<rbrakk>
     \<Longrightarrow> accepts M (splice (length (enc0 as s) + offR as s kk j)
                          (W as s) (enc as s kk) (to_bits (W as s) u))
         \<longleftrightarrow> (\<exists>xs\<in>bitvec (length as). rhs_of as kk s xs = u \<and>
                              lhs_of as kk xs \<in> set (enumL as s kk))"
  assumes read0_after_enc0:
    "Base.read0 M (enc as s kk)
       \<subseteq> { length (enc0 as s)
          ..< length (enc0 as s) + length (padL as s kk) + length (padR as s kk) }"

begin

abbreviation x0 :: "int list \<Rightarrow> int \<Rightarrow> bool list" where
  "x0 as s \<equiv> enc as s kk"

definition touches :: "bool list \<Rightarrow> nat set \<Rightarrow> bool" where
  "touches x B \<longleftrightarrow> Base.read0 M x \<inter> B \<noteq> {}"

lemma offL_window_in_enc:
  assumes jL: "j < length (enumL as s kk)"
  shows "length (enc0 as s) + offL as s j + W as s \<le> length (enc as s kk)"
proof -
  have pad_bound:
    "offL as s j + W as s \<le> length (padL as s kk) + length (padR as s kk)"
  proof -
    have "(Suc j) * W as s
            \<le> (length (enumL as s kk) + length (enumR as s kk)) * W as s"
      using jL by (intro mult_right_mono) simp_all
    then show ?thesis
      by (simp add: offL_def length_padL length_padR add_mult_distrib2 algebra_simps)
  qed

  have "length (enc0 as s) + offL as s j + W as s
        = length (enc0 as s) + (offL as s j + W as s)" by simp
  also have "\<dots> \<le> length (enc0 as s) + (length (padL as s kk) + length (padR as s kk))"
    using pad_bound by (rule add_left_mono)
  also have "\<dots> = length (enc as s kk)"
    by (simp add: enc_def)
  finally show ?thesis .
qed

lemma offR_window_in_enc:
  assumes jR: "j < length (enumR as s kk)"
  shows "length (enc0 as s) + offR as s kk j + W as s \<le> length (enc as s kk)"
proof -
  have "(Suc j) * W as s \<le> length (enumR as s kk) * W as s"
    using jR by (intro mult_right_mono) simp_all
  hence offR_le:
    "offR as s kk j + W as s \<le> length (padL as s kk) + length (padR as s kk)"
    by (simp add: offR_def length_padL length_padR add_mult_distrib2 algebra_simps)
  then show ?thesis
    by (simp add: enc_def add_left_mono)
qed

definition Lval_at :: "int list \<Rightarrow> int \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> int" where
  "Lval_at as s oL j =
     from_bits (map oL [length (enc0 as s) + offL as s j  ..<  length (enc0 as s) + offL as s j + W as s])"

definition Rval_at :: "int list \<Rightarrow> int \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> int" where
  "Rval_at as s oR j =
     from_bits (map oR [length (enc0 as s) + offR as s kk j ..<  length (enc0 as s) + offR as s kk j + W as s])"

(* 1) The index sets we want fully covered *)
definition Lset where
  "Lset as s \<equiv> \<Union> j < length (enumL as s kk). blockL_abs enc0 as s j"

definition Rset where
  "Rset as s \<equiv> \<Union> j < length (enumR as s kk). blockR_abs enc0 as s kk j"

(* 2) The decision tree extracted from the TM on input x = enc as s kk *)
definition T where
  "T as s \<equiv>
     tm_to_dtr' head0 stepf final_acc
       (steps M (enc as s kk))
       (conf M (enc as s kk) 0)"

(* 3) The semantic predicate that the DT computes (pure spec; no bitstrings) *)
definition good where
  "good as s oL oR \<equiv>
     (\<exists>jL<length (enumL as s kk). \<exists>jR<length (enumR as s kk).
        Lval_at as s oL jL = Rval_at as s oR jR)"

lemma in_padL_imp_in_some_blockL_abs:
  assumes i_in:
    "i \<in> {length (enc0 as s) ..< length (enc0 as s) + length (padL as s kk)}"
  shows "\<exists>j<length (enumL as s kk). i \<in> blockL_abs enc0 as s j"
proof -
  let ?len0 = "length (enc0 as s)"
  let ?W    = "W as s"
  let ?E    = "enumL as s kk"
  let ?k    = "i - ?len0"

  have i_ge: "?len0 \<le> i" and i_lt: "i < ?len0 + length (padL as s kk)"
    using i_in by auto
  hence k_lt: "?k < length (padL as s kk)" by simp

  (* From membership, the padL interval is non-empty \<rightarrow> W > 0 *)
  have Wpos: "0 < ?W"
  proof (rule ccontr)
    assume "\<not> 0 < ?W" hence "?W = 0" by simp
    hence "length (padL as s kk) = 0" by (simp add: length_padL)
    have "length (padL as s kk) = 0" by (simp add: \<open>length (padL as s kk) = 0\<close>)
    then have "i \<in> {length (enc0 as s) ..< length (enc0 as s) + 0}" using i_in by simp
    thus False by simp
  qed

  (* length padL is (#enumL) * W *)
  have padL_len: "length (padL as s kk) = length ?E * ?W"
    by (simp add: length_padL)

  define j where "j = ?k div ?W"
  have j_lt: "j < length ?E"
    using k_lt Wpos by (simp add: j_def padL_len div_less_iff_less_mult)

  (* decompose k = j*W + r, with r < W *)
  have decomp: "?k = j * ?W + (?k mod ?W)"
    by (simp add: j_def mult.commute div_mult_mod_eq)
  have r_lt: "(?k mod ?W) < ?W"
    using Wpos by (rule mod_less_divisor)

  (* rewrite the block and show membership *)
  have "i = ?len0 + j * ?W + (?k mod ?W)"
    using i_ge decomp by simp
  moreover have
    "blockL_abs enc0 as s j = { ?len0 + j * ?W ..< ?len0 + j * ?W + ?W }"
    by (simp add: blockL_abs_def offL_def)
  ultimately have "i \<in> blockL_abs enc0 as s j"
    using r_lt by auto

  thus ?thesis by (intro exI[of _ j]) (use j_lt in simp)
qed

lemma in_padR_imp_in_some_blockR_abs:
  assumes iR:
    "i \<in> { length (enc0 as s) + length (padL as s kk)
         ..< length (enc0 as s) + length (padL as s kk) + length (padR as s kk) }"
  shows "\<exists>j<length (enumR as s kk). i \<in> blockR_abs enc0 as s kk j"
proof -
  let ?base = "length (enc0 as s) + length (padL as s kk)"
  let ?W    = "W as s"
  let ?r    = "i - ?base"

  from iR have base_le: "?base \<le> i"
    and r_lt: "?r < length (padR as s kk)"
    by auto

  have padR_len: "length (padR as s kk) = length (enumR as s kk) * ?W"
    by (simp add: length_padR)

  (* show W>0; otherwise padR would be empty, contradicting r_lt *)
  have Wpos: "0 < ?W"
  proof (rule ccontr)
    assume "\<not> 0 < ?W"
    then have "?W = 0" by simp
    then have "length (padR as s kk) = 0" by (simp add: padR_len)
    with r_lt show False by simp
  qed

  define j where "j = ?r div ?W"
  define u where "u = ?r mod ?W"

  have j_lt: "j < length (enumR as s kk)"
    using r_lt Wpos by (simp add: j_def padR_len div_less_iff_less_mult)

  have u_lt: "u < ?W"
    using Wpos by (simp add: u_def)

(* from iR you likely already have: *)
  have base_le: "?base \<le> i" and r_lt: "i - ?base < length (padR as s kk)"
    using iR by auto

(* You also proved 0 < ?W as Wpos earlier. Now the decomposition: *)
  have i_decomp:
    "i = ?base
        + ((i - ?base) div ?W) * ?W
        + ((i - ?base) mod ?W)"
  proof -
    have "(i - ?base) = ((i - ?base) div ?W) * ?W + ((i - ?base) mod ?W)"
      using Wpos by (simp add: div_mult_mod_eq)
    then show ?thesis using base_le by linarith
  qed

  have BR_eq:
    "blockR_abs enc0 as s kk j
     = { ?base + j * ?W ..< ?base + j * ?W + ?W }"
    using blockR_abs_def offR_def by (simp add: add.assoc length_padL)

have u_ge0: "0 \<le> u" by simp   (* nat is nonnegative *)

have mem:
  "length (enc0 as s) + length (padL as s kk) + j * W as s \<le> i \<and>
   i < length (enc0 as s) + length (padL as s kk) + j * W as s + W as s"
  using i_decomp j_def u_def u_lt by force

have "i \<in> blockR_abs enc0 as s kk j"
  using mem
  by (simp add: BR_eq)

  thus ?thesis using j_lt by blast
qed

lemma read0_subset_blocks_abs:
  "Base.read0 M (enc as s kk) \<subseteq> Lset as s \<union> Rset as s"
proof
  fix i assume iR: "i \<in> Base.read0 M (enc as s kk)"

  have len_enc:
    "length (enc as s kk)
     = length (enc0 as s) + length (padL as s kk) + length (padR as s kk)"
    by (simp add: enc_def)

  (* 1) First, land i in the big half-open interval after enc0 *)
  from read0_after_enc0 iR have i_band:
    "i \<in> { length (enc0 as s)
         ..< length (enc0 as s) + length (padL as s kk) + length (padR as s kk) }"
    by (rule subsetD)

  (* 2) Split i_band into the two inequalities we will feed to the L/R lemmas *)
  have base_le:   "length (enc0 as s) \<le> i"
    and  i_lt_enc: "i < length (enc0 as s) + length (padL as s kk) + length (padR as s kk)"
    using i_band by auto

  (* 3) Case split: i lies either in padL or in padR *)
  have disj:
    "i < length (enc0 as s) + length (padL as s kk) \<or>
     length (enc0 as s) + length (padL as s kk) \<le> i" by linarith

  from disj show "i \<in> Lset as s \<union> Rset as s"
  proof
    (* ---- L-branch ---- *)
    assume i_lt_L: "i < length (enc0 as s) + length (padL as s kk)"
    have i_in_padL_set:
      "i \<in> { length (enc0 as s) ..< length (enc0 as s) + length (padL as s kk) }"
      using base_le i_lt_L by simp
    from in_padL_imp_in_some_blockL_abs[OF i_in_padL_set]
    obtain j where jL: "j < length (enumL as s kk)"
               and iBL: "i \<in> blockL_abs enc0 as s j" by blast
    have "i \<in> Lset as s"
      unfolding Lset_def by (intro UN_I[of j]) (use jL iBL in auto)
    thus ?thesis by simp

  next
    (* ---- R-branch ---- *)
    assume ge: "length (enc0 as s) + length (padL as s kk) \<le> i"
    have i_in_padR_set:
      "i \<in> { length (enc0 as s) + length (padL as s kk)
           ..< length (enc0 as s) + length (padL as s kk) + length (padR as s kk) }"
      using ge i_lt_enc by simp
    from in_padR_imp_in_some_blockR_abs[OF i_in_padR_set]
    obtain j where jR: "j < length (enumR as s kk)"
               and iBR: "i \<in> blockR_abs enc0 as s kk j" by blast
    have "i \<in> Rset as s"
      unfolding Rset_def by (intro UN_I[of j]) (use jR iBR in auto)
    thus ?thesis by simp
  qed
qed

(* 4) Well-formedness of T wrt declared index sets (no out-of-set queries)
   This is just bookkeeping: T only ever asks absolute indices that lie
   in Lset \<union> Rset by construction of the encoder. *)
lemma wf_T:
  "wf_dtr (Lset as s) (Rset as s)
          (tm_to_dtr' head0 stepf final_acc (steps M (enc as s kk))
            (conf M (enc as s kk) 0))"
proof -
  let ?x = "enc as s kk"
  let ?T = "tm_to_dtr' head0 stepf final_acc (steps M ?x) (conf M ?x 0)"

  have SL1:
    "seenL_run ((!) ?x) ((!) ?x) ?T
       \<subseteq> (\<lambda>u. nat (head0 (drive u (conf M ?x 0) ((!) ?x)))) ` {..< steps M ?x}"
    by (rule seenL_tm_to_dtr_subset_read0_helper)

  have SL0:
    "seenL_run ((!) ?x) ((!) ?x) ?T \<subseteq> Base.read0 M ?x"
    using SL1 by (simp add: drive_conf Base.read0_def)

  have SR1:
    "seenR_run ((!) ?x) ((!) ?x) ?T
       \<subseteq> (\<lambda>u. nat (head0 (drive u (conf M ?x 0) ((!) ?x)))) ` {..< steps M ?x}"
    by (rule seenR_tm_to_dtr_subset_read0_helper)

  have SR0:
    "seenR_run ((!) ?x) ((!) ?x) ?T \<subseteq> Base.read0 M ?x"
    using SR1 by (simp add: drive_conf Base.read0_def)

  have R0_sub: "Base.read0 M ?x \<subseteq> Lset as s \<union> Rset as s"
    by (rule read0_subset_blocks_abs)

  have SL: "seenL_run ((!) ?x) ((!) ?x) ?T \<subseteq> Lset as s \<union> Rset as s"
    using SL0 R0_sub by auto
  have SR: "seenR_run ((!) ?x) ((!) ?x) ?T \<subseteq> Lset as s \<union> Rset as s"
    using SR0 R0_sub by auto

  show ?thesis
    using SL SR by (meson correctness)
qed

(* 5) Correctness of the tree wrt the spec *)
lemma correct_T:
  "run (\<lambda>i. (enc as s kk) ! i) (\<lambda>j. (enc as s kk) ! j) (T as s)
   = good as s (\<lambda>i. (enc as s kk) ! i) (\<lambda>j. (enc as s kk) ! j)"
proof -
  have "run (\<lambda>i. (enc as s kk) ! i) (\<lambda>j. (enc as s kk) ! j) (T as s)
        = run ((!) (enc as s kk)) ((!) (enc as s kk))
             (tm_to_dtr' head0 stepf final_acc (steps M (enc as s kk))
                (conf M (enc as s kk) 0))"
    by (simp add: T_def)
  also have "\<dots> = accepts M (enc as s kk)"
    by (simp add: tm_to_dtr_accepts)   (* from DTM_Run_Sem context *)
  also have "\<dots> = good as s (\<lambda>i. (enc as s kk) ! i) (\<lambda>j. (enc as s kk) ! j)"
    by (simp add: correctness)
  finally show ?thesis .
qed

lemma nth_concat_map_fixed:
  fixes xs :: "'a list" and f :: "'a \<Rightarrow> 'b list" and w :: nat
  assumes LEN: "\<And>x. x \<in> set xs \<Longrightarrow> length (f x) = w"
    and j: "j < length xs"
    and t: "t < w"
  shows "concat (map f xs) ! (j*w + t) = f (xs!j) ! t"
proof -
  (* 1) length of the concatenation over the first j chunks is j*w *)
  have pref_len: "length (concat (map f (take j xs))) = j * w"
  proof -
    have "length (concat (map f (take j xs)))
        = sum_list (map (length \<circ> f) (take j xs))"
      by (simp add: length_concat)
    also have "... = (\<Sum>_\<leftarrow> take j xs. w)"
      by (smt (verit) LEN comp_apply in_set_takeD map_eq_conv)
    also have "... = length (take j xs) * w"
      by (simp add: sum_const_all_nat)
    also have "... = j * w"
      using length_take min_def by (simp add: j)
    finally show ?thesis .
  qed

(* 2) split the big concat at chunk j *)
  have map_split:
    "map f xs = map f (take j xs) @ [f (xs ! j)] @ map f (drop (Suc j) xs)"
    using j Cons_nth_drop_Suc append_Cons append_Nil append_take_drop_id list.simps(9) map_append 
    by metis

  have split:
    "concat (map f xs)
     = concat (map f (take j xs)) @ f (xs ! j)
       @ concat (map f (drop (Suc j) xs))"
    using map_split concat_append by simp

  (* 3) index into the middle block *)
  from t have "concat (map f xs) ! (j*w + t)
             = (f (xs!j) @ concat (map f (drop (Suc j) xs))) ! t"
    by (simp add: split pref_len nth_append)
  also from t have "... = f (xs!j) ! t"
    using LEN j by (simp add: nth_append)
  finally show ?thesis .
qed

lemma Rval_at_on_enc_block:
  fixes j :: nat
  assumes jR: "j < length (enumR as s kk)"
  shows "Rval_at as s (\<lambda>i. (enc as s kk) ! i) j = enumR as s kk ! j"
proof -
  let ?a = "length (enc0 as s) + offR as s kk j"
  let ?w = "W as s"

  have map_slice_R:
    "map ((!) (x0 as s)) [?a ..< ?a + ?w]
     = to_bits (W as s) (enumR as s kk ! j)"
  proof (rule nth_equalityI)
    (* lengths match: the slice has length w, and each catalog block is length w *)
    show "length (map ((!) (x0 as s)) [?a ..< ?a + ?w])
          = length (to_bits (W as s) (enumR as s kk ! j))"
      using jR to_bits_len_on_enumR in_set_conv_nth
      by (metis diff_add_inverse length_map length_upt)

  next
    fix t assume t: "t < length (map ((!) (x0 as s)) [?a ..< ?a + ?w])"
    hence tw: "t < ?w" by simp
    have idx: "[?a ..< ?a + ?w] ! t = ?a + t" using tw by simp

    (* rewrite absolute offset through enc = enc0 @ padL @ padR *)
    have a_decomp: "?a = length (enc0 as s) + length (padL as s kk) + j * ?w"
      by (simp add: offR_def length_padL)

    have step_enc_pad:
      "(x0 as s) ! (?a + t) = (padR as s kk) ! (j * ?w + t)"
      using enc_def a_decomp nth_append_length_plus 
      by (simp add: add.assoc)

    (* fixed-width chunks inside padR *)
    have fixed_len_meta:
      "\<And>x. x \<in> set (enumR as s kk) \<Longrightarrow> length (to_bits (W as s) x) = ?w"
      by (simp add: to_bits_len_on_enumR)

    have "map ((!) (x0 as s)) [?a ..< ?a + ?w] ! t
          = (x0 as s) ! (?a + t)" 
      using nth_map idx t by auto
    also have "... = concat (map (to_bits ?w) (enumR as s kk)) ! (j * ?w + t)"
      by (simp add: step_enc_pad padR_def)
    also have "... = to_bits ?w (enumR as s kk ! j) ! t"
      by (rule nth_concat_map_fixed[OF fixed_len_meta jR tw])
    finally show
      "map ((!) (x0 as s)) [?a ..< ?a + ?w] ! t
       = to_bits (W as s) (enumR as s kk ! j) ! t" .
  qed

  have "Rval_at as s ((!) (x0 as s)) j
        = from_bits (to_bits (W as s) (enumR as s kk ! j))"
    by (simp add: Rval_at_def map_slice_R)

  have v_inR: "enumR as s kk ! j \<in> set (enumR as s kk)"
    using jR in_set_conv_nth by metis

  have v_inU:
    "enumR as s kk ! j \<in> set (enumL as s kk) \<union> set (enumR as s kk)"
    using v_inR by (rule UnI2)

  have "from_bits (to_bits (W as s) (enumR as s kk ! j))
        = enumR as s kk ! j"
    using bits_roundtrip[OF v_inU] by simp

  have "Rval_at as s ((!) (x0 as s)) j
        = from_bits (to_bits (W as s) (enumR as s kk ! j))"
    by (simp add: Rval_at_def map_slice_R)
  also have "... = enumR as s kk ! j"
    using bits_roundtrip[OF v_inU] by simp
  finally show ?thesis .
qed

lemma R_catalog_for_enc:
  "set (map (Rval_at as s (\<lambda>i. (enc as s kk) ! i))
             [0..<length (enumR as s kk)])
   = set (enumR as s kk)"
proof -
  let ?n = "length (enumR as s kk)"
  have map_eq:
    "map (Rval_at as s ((!) (x0 as s))) [0..<?n]
     = map (\<lambda>j. enumR as s kk ! j) [0..<?n]"
    by (rule map_cong[OF _])
       (simp_all add: Rval_at_on_enc_block)

  have set_map_nth:
    "set (map (\<lambda>j. enumR as s kk ! j) [0..<?n]) = set (enumR as s kk)"
    using set_conv_nth by (simp add: map_nth)

  show ?thesis
    using map_eq set_map_nth by force
qed

lemma flipL_pointwise_enc:
  fixes j :: nat
  assumes jL:  "j < length (enumL as s kk)"
      and L2:  "2 \<le> length (enumL as s kk)"
      and hit:  "\<exists>v\<in>set (enumL as s kk). v \<in> set (enumR as s kk)"
      and miss: "\<exists>v\<in>set (enumL as s kk). v \<notin> set (enumR as s kk)"
      and baseline_only_j:
        "good as s ((!) (x0 as s)) ((!) (x0 as s)) \<longrightarrow>
         (\<forall>j'<length (enumL as s kk). j' \<noteq> j \<longrightarrow>
            Lval_at as s ((!) (x0 as s)) j' \<notin> set (enumR as s kk))"
  shows "\<exists>oL'. (\<forall>i. i \<notin> blockL_abs enc0 as s j \<longrightarrow> oL' i = (x0 as s) ! i)
              \<and> good as s oL' ((!) (x0 as s))
                \<noteq> good as s ((!) (x0 as s)) ((!) (x0 as s))"
proof -
  obtain v_in where v_inL: "v_in \<in> set (enumL as s kk)" and v_inR: "v_in \<in> set (enumR as s kk)"
    using hit by blast
  obtain v_out where v_outL: "v_out \<in> set (enumL as s kk)" and v_outNR: "v_out \<notin> set (enumR as s kk)"
    using miss by blast

  let ?a = "length (enc0 as s) + offL as s j"
  let ?w = "W as s"

  obtain bv_in  where bv_in_len:  "length bv_in  = ?w" and bv_in_val:  "from_bits bv_in  = v_in"
    using v_inL bits_roundtrip by blast
  obtain bv_out where bv_out_len: "length bv_out = ?w" and bv_out_val: "from_bits bv_out = v_out"
    using v_outL bits_roundtrip by blast

  define oL_in  where "oL_in  i = (if i \<in> blockL_abs enc0 as s j then bv_in  ! (i - ?a) else (x0 as s) ! i)" for i
  define oL_out where "oL_out i = (if i \<in> blockL_abs enc0 as s j then bv_out ! (i - ?a) else (x0 as s) ! i)" for i

  have blk_eq: "blockL_abs enc0 as s j = {?a ..< ?a + ?w}"
    by (simp add: blockL_abs_def offL_def)

  (* values read from block j under the two overwrites *)
  have Lval_in:  "Lval_at as s oL_in  j = v_in"
  proof -
    have slice: "map oL_in [?a ..< ?a + ?w] = bv_in"
    proof (rule nth_equalityI)
      show "length (map oL_in [?a ..< ?a + ?w]) = length bv_in" by (simp add: bv_in_len)
    next
      fix t assume "t < length (map oL_in [?a ..< ?a + ?w])"
      hence tw: "t < ?w" by simp
      have idx: "[?a ..< ?a + ?w] ! t = ?a + t" using tw by simp
      have inblk: "?a + t \<in> blockL_abs enc0 as s j" using tw by (simp add: blk_eq)
      show "map oL_in [?a ..< ?a + ?w] ! t = bv_in ! t"
        using nth_map idx oL_in_def inblk by (simp add: tw)
    qed
    show ?thesis by (simp add: Lval_at_def slice bv_in_val)
  qed

  have Lval_out: "Lval_at as s oL_out j = v_out"
  proof -
    have slice: "map oL_out [?a ..< ?a + ?w] = bv_out"
    proof (rule nth_equalityI)
      show "length (map oL_out [?a ..< ?a + ?w]) = length bv_out" by (simp add: bv_out_len)
    next
      fix t assume "t < length (map oL_out [?a ..< ?a + ?w])"
      hence tw: "t < ?w" by simp
      have idx: "[?a ..< ?a + ?w] ! t = ?a + t" using tw by simp
      have inblk: "?a + t \<in> blockL_abs enc0 as s j" using tw by (simp add: blk_eq)
      show "map oL_out [?a ..< ?a + ?w] ! t = bv_out ! t"
        using nth_map idx oL_out_def inblk by (simp add: tw)
    qed
    show ?thesis by (simp add: Lval_at_def slice bv_out_val)
  qed

  (* unchanged slices for j' \<noteq> j *)
  have same_block:
    "\<And>j'. j' \<noteq> j \<Longrightarrow> Lval_at as s oL_out j' = Lval_at as s ((!) (x0 as s)) j'"
  proof -
    fix j' assume ne: "j' \<noteq> j"
    let ?a' = "length (enc0 as s) + offL as s j'"
    let ?w' = "W as s"
    have blk': "blockL_abs enc0 as s j' = {?a' ..< ?a' + ?w'}"
      by (simp add: blockL_abs_def offL_def)
    have slice_eq:
      "map oL_out [?a' ..< ?a' + ?w'] = map ((!) (x0 as s)) [?a' ..< ?a' + ?w']"
    proof (rule nth_equalityI)
      show "length (map oL_out [?a' ..< ?a' + ?w'])
            = length (map ((!) (x0 as s)) [?a' ..< ?a' + ?w'])" by simp
    next
      fix t assume "t < length (map oL_out [?a' ..< ?a' + ?w'])"
      hence tw: "t < ?w'" by simp
      have idx: "[?a' ..< ?a' + ?w'] ! t = ?a' + t" using tw by simp
      have in_j': "?a' + t \<in> blockL_abs enc0 as s j'" using tw by (simp add: blk')
      have not_in_j: "?a' + t \<notin> blockL_abs enc0 as s j"
        using blockL_abs_disjoint[OF ne] in_j' by auto
      have out_eq: "oL_out (?a' + t) = (x0 as s) ! (?a' + t)"
        by (simp add: oL_out_def not_in_j)
      show "map oL_out [?a' ..< ?a' + ?w'] ! t
            = map ((!) (x0 as s)) [?a' ..< ?a' + ?w'] ! t"
        using nth_map idx out_eq by (simp add: tw)
    qed
    show "Lval_at as s oL_out j' = Lval_at as s ((!) (x0 as s)) j'"
      by (simp add: Lval_at_def slice_eq)
  qed

  (* R-catalog char and “good” characterization *)
  have R_catalog:
    "set (map (Rval_at as s ((!) (x0 as s))) [0..<length (enumR as s kk)])
     = set (enumR as s kk)"
    by (rule R_catalog_for_enc)

  have Good_char:
    "good as s oL ((!) (x0 as s))
     \<longleftrightarrow> (\<exists>jL<length (enumL as s kk). Lval_at as s oL jL \<in> set (enumR as s kk))"
    for oL
  proof
    assume "good as s oL ((!) (x0 as s))"
    then obtain jL jR where jL: "jL < length (enumL as s kk)" and jR: "jR < length (enumR as s kk)"
      and eq: "Lval_at as s oL jL = Rval_at as s ((!) (x0 as s)) jR"
      by (auto simp: good_def)
    hence "Lval_at as s oL jL \<in> set (enumR as s kk)"
      using R_catalog jR by (auto simp: in_set_conv_nth)
    thus "\<exists>jL<length (enumL as s kk). Lval_at as s oL jL \<in> set (enumR as s kk)" using jL by blast
  next
    assume "\<exists>jL<length (enumL as s kk). Lval_at as s oL jL \<in> set (enumR as s kk)"
    then obtain jL where jL: "jL < length (enumL as s kk)"
      and mem: "Lval_at as s oL jL \<in> set (enumR as s kk)" by blast
    then obtain jR where jR: "jR < length (enumR as s kk)"
      and eq:  "Lval_at as s oL jL = enumR as s kk ! jR"
      using in_set_conv_nth by metis
    hence "Lval_at as s oL jL = Rval_at as s ((!) (x0 as s)) jR"
      by (simp add: Rval_at_on_enc_block jR)
    thus "good as s oL ((!) (x0 as s))" using jL jR by (auto simp: good_def)
  qed

  (* baseline split *)
  show ?thesis
  proof (cases "good as s ((!) (x0 as s)) ((!) (x0 as s))")
    case True
    (* by uniqueness, no other j' witnesses baseline *)
    have no_other:
      "\<And>j'. j' < length (enumL as s kk) \<Longrightarrow> j' \<noteq> j \<Longrightarrow>
         Lval_at as s ((!) (x0 as s)) j' \<notin> set (enumR as s kk)"
      using baseline_only_j True by blast

    have not_good_out: "\<not> good as s oL_out ((!) (x0 as s))"
    proof
      assume H: "good as s oL_out ((!) (x0 as s))"
      then obtain j' where j'lt: "j' < length (enumL as s kk)"
        and mem': "Lval_at as s oL_out j' \<in> set (enumR as s kk)"
        by (auto simp: Good_char)
      show False
      proof (cases "j' = j")
        case True
        with Lval_out v_outNR show False
        using mem' by blast
      next
        case False
        have "Lval_at as s ((!) (x0 as s)) j' \<in> set (enumR as s kk)"
          using same_block[OF False] mem' by simp
        with no_other[OF j'lt False] show False by contradiction
      qed
    qed

    have outside_out: "\<forall>i. i \<notin> blockL_abs enc0 as s j \<longrightarrow> oL_out i = (x0 as s) ! i"
      by (simp add: oL_out_def)

    show ?thesis
      by (intro exI[of _ oL_out]) (use outside_out True not_good_out in auto)

  next
    case False
    (* create a witness at j *)
    have good_in': "good as s oL_in ((!) (x0 as s))"
      using Good_char jL Lval_in v_inR by blast

    have outside_in: "\<forall>i. i \<notin> blockL_abs enc0 as s j \<longrightarrow> oL_in i = (x0 as s) ! i"
      by (simp add: oL_in_def)

    show ?thesis
      by (intro exI[of _ oL_in]) (use outside_in False good_in' in auto)
  qed
qed

lemma run_agrees_on_seen:
  fixes T :: "('i,'j) dtr"
  assumes L: "\<And>i. i \<in> seenL_run oL oR T \<Longrightarrow> oL i = oL' i"
      and R: "\<And>j. j \<in> seenR_run oL oR T \<Longrightarrow> oR j = oR' j"
  shows "run oL oR T = run oL' oR' T"
  using L R by (induction T) auto

lemma flipR_pointwise_block:
  fixes oL oR :: "nat \<Rightarrow> bool" and j :: nat
  assumes jR: "j < length (enumR as s kk)"
      and R2: "2 \<le> length (enumR as s kk)"
  shows "\<exists>oR'.
           (\<forall>i. i \<notin> blockR_abs enc0 as s kk j \<longrightarrow> oR' i = oR i)
         \<and> Rval_at as s oR' j \<noteq> Rval_at as s oR j"
proof -
  (* pick two different catalog values from enumR *)
  have len1: "1 < length (enumR as s kk)" using R2 by simp

  define u where "u = enumR as s kk ! 0"
  define v where "v = enumR as s kk ! 1"

  have u_in: "u \<in> set (enumR as s kk)"
    unfolding u_def nth_mem R2 by (meson len1 nth_mem order.strict_trans zero_less_one)
  have v_in: "v \<in> set (enumR as s kk)"
    unfolding v_def by (meson len1 nth_mem order.strict_trans zero_less_one)

  have distinct_enumR: "distinct (enumR as s kk)"
    by (simp add: enumR_def)  (* sorted_list_of_set -> distinct *)
  have uv_ne: "u \<noteq> v"
    using distinct_enumR R2 len1 distinct_conv_nth
    unfolding u_def v_def
    by (metis length_pos_if_in_set u_in zero_neq_one)

  let ?a = "length (enc0 as s) + offR as s kk j"
  let ?w = "W as s"

  (* fixed-width bit patterns for u and v *)
  obtain bu where bu_len: "length bu = ?w" and bu_val: "from_bits bu = u"
    using u_in bits_roundtrip by blast
  obtain bv where bv_len: "length bv = ?w" and bv_val: "from_bits bv = v"
    using v_in bits_roundtrip by blast

  (* overwrite the whole j-th R block with bits for v *)
  define oR' where
    "oR' i = (if ?a \<le> i \<and> i < ?a + ?w then bv ! (i - ?a) else oR i)" for i

  have outside_eq: "\<And>i. i \<notin> blockR_abs enc0 as s kk j \<Longrightarrow> oR' i = oR i"
    by (auto simp: oR'_def blockR_abs_def)

  (* slice [a ..< a+w] becomes exactly bv under oR' *)
  have slice_bv: "map oR' [?a ..< ?a + ?w] = bv"
  proof (rule nth_equalityI)
    show "length (map oR' [?a ..< ?a + ?w]) = length bv"
      by (simp add: bv_len)
  next
    fix i assume i_len: "i < length (map oR' [?a ..< ?a + ?w])"
    hence iw: "i < ?w" by simp
    have idx: "[?a ..< ?a + ?w] ! i = ?a + i"
      using iw by simp
    have inblk: "?a \<le> ?a + i \<and> ?a + i < ?a + ?w"
      using iw by simp
    show "map oR' [?a ..< ?a + ?w] ! i = bv ! i"
      using nth_map idx oR'_def inblk by simp
  qed

  have new_val: "Rval_at as s oR' j = v"
    by (simp add: Rval_at_def slice_bv bv_val)

  (* either we already differ from v, or we first overwrite to u, which differs from v *)
  consider (diff) "Rval_at as s oR j \<noteq> v" | (eqv) "Rval_at as s oR j = v" by blast
  then show ?thesis
  proof cases
    case diff
    with outside_eq new_val show ?thesis by metis
  next
    case eqv
    (* overwrite to u to force a difference *)
    define oR_u where
      "oR_u i = (if ?a \<le> i \<and> i < ?a + ?w then bu ! (i - ?a) else oR i)" for i
    have slice_bu: "map oR_u [?a ..< ?a + ?w] = bu"
    proof (rule nth_equalityI)
      show "length (map oR_u [?a ..< ?a + ?w]) = length bu"
        by (simp add: bu_len)
    next
      fix i assume i_len: "i < length (map oR_u [?a ..< ?a + ?w])"
      hence iw: "i < ?w" by simp
      have idx: "[?a ..< ?a + ?w] ! i = ?a + i"
        using iw by simp
      have inblk: "?a \<le> ?a + i \<and> ?a + i < ?a + ?w"
        using iw by simp
      show "map oR_u [?a ..< ?a + ?w] ! i = bu ! i"
        using nth_map idx oR_u_def inblk by simp
    qed
    have old_to_u: "Rval_at as s oR_u j = u"
      by (simp add: Rval_at_def slice_bu bu_val)
    have diff_now: "Rval_at as s oR_u j \<noteq> Rval_at as s oR j"
      using eqv old_to_u uv_ne by simp
    have outside_eq_u: "\<forall>i. i \<notin> blockR_abs enc0 as s kk j \<longrightarrow> oR_u i = oR i"
      by (simp add: oR_u_def blockR_abs_def)
    from outside_eq_u diff_now show ?thesis by blast
  qed
qed

definition L0   where "L0 as s   = Lset as s"
definition R0   where "R0 as s   = Rset as s"
definition T0   where "T0 as s   = T as s"
definition Good where "Good as s = good as s"

(* Re-prove the four obligations with arguments applied *)
lemma wf_T0:
  "wf_dtr (L0 as s) (R0 as s) (T0 as s)"
  unfolding L0_def R0_def T0_def
  using wf_T by (simp add: T_def)

lemma correct_T0:
  "run (\<lambda>i. (enc as s kk) ! i) (\<lambda>j. (enc as s kk) ! j) (T0 as s)
   = Good as s (\<lambda>i. (enc as s kk) ! i) (\<lambda>j. (enc as s kk) ! j)"
  unfolding T0_def Good_def
  by (rule correct_T)

lemma Lval_at_on_enc_block:
  assumes jL: "j < length (enumL as s kk)"
  shows "Lval_at as s ((!) (x0 as s)) j = enumL as s kk ! j"
proof -
  let ?a = "length (enc0 as s) + offL as s j"
  let ?w = "W as s"
  have blk_eq: "blockL_abs enc0 as s j = {?a ..< ?a + ?w}"
    by (simp add: blockL_abs_def offL_def)

  have slice:
    "map ((!) (x0 as s)) [?a ..< ?a + ?w] = to_bits (W as s) (enumL as s kk ! j)"
  proof (rule nth_equalityI)
    have v_inL: "enumL as s kk ! j \<in> set (enumL as s kk)"
      using jL in_set_conv_nth by metis
    have len_tobits[simp]:
      "length (to_bits (W as s) (enumL as s kk ! j)) = W as s"
      using to_bits_len_on_enumL v_inL by simp
    show "length (map ((!) (x0 as s)) [?a ..< ?a + ?w])
          = length (to_bits (W as s) (enumL as s kk ! j))"
      using jL to_bits_len_on_enumL comp_def by (simp add: comp_def)
  next
    fix t assume "t < length (map ((!) (x0 as s)) [?a ..< ?a + ?w])"
    hence tw: "t < ?w" by simp
    have idx: "[?a ..< ?a + ?w] ! t = ?a + t" using tw by simp
    (* x0 = enc0 @ padL @ padR; this index falls in padL’s j-th chunk *)
    have step_enc_pad:
      "(x0 as s) ! (length (enc0 as s) + offL as s j + t)
   = concat (map (to_bits (W as s)) (enumL as s kk)) ! (j * W as s + t)"
    proof -
      let ?w = "W as s"
        (* show the index points into padL *)
      have less_padL: "offL as s j + t < length (padL as s kk)"
      proof -
        have jpart: "j * ?w + t < (Suc j) * ?w"
          using tw by (simp add: add_mult_distrib2)
        have mono: "(Suc j) * ?w \<le> length (enumL as s kk) * ?w"
          using jL by (intro mult_right_mono) simp_all
        from jpart mono show ?thesis
          by (simp add: offL_def length_padL less_le_trans)
      qed
  (* push through enc0 and then select the padL half *)
      have "(x0 as s) ! (length (enc0 as s) + offL as s j + t)
        = (enc0 as s @ padL as s kk @ padR as s kk) !
            (length (enc0 as s) + offL as s j + t)"
        by (simp add: enc_def)
      also have "... = (padL as s kk @ padR as s kk) ! (offL as s j + t)"
        using nth_append_length_plus
        by (simp add: add.assoc)
      also have "... = padL as s kk ! (offL as s j + t)"
        using less_padL by (simp add: nth_append)
      also have "... =
        concat (map (to_bits ?w) (enumL as s kk)) ! (j * ?w + t)"
        by (simp add: padL_def offL_def add_mult_distrib2)
      finally show ?thesis .
    qed
    have fixed_len_meta:
      "\<And>v. v \<in> set (enumL as s kk) \<Longrightarrow> length (to_bits (W as s) v) = ?w"
        by (simp add: to_bits_len_on_enumL)
    have fixed_len_meta:
      "\<And>x'. x' \<in> set (enumL as s kk) \<Longrightarrow> length (to_bits (W as s) x') = W as s"
      by (simp add: to_bits_len_on_enumL)
    thus "map ((!) (x0 as s)) [?a ..< ?a + ?w] ! t
          = to_bits (W as s) (enumL as s kk ! j) ! t"
      using nth_map idx
      by (smt (verit) \<open>t < length (map ((!) (x0 as s)) 
        [length (enc0 as s) + offL as s j..< 
        length (enc0 as s) + offL as s j + W as s])\<close> jL 
        length_map nth_concat_map_fixed step_enc_pad tw)
  qed
  have v_in: "enumL as s kk ! j \<in> set (enumL as s kk)"
    using jL in_set_conv_nth by metis
  have round: "from_bits (to_bits (W as s) (enumL as s kk ! j)) = enumL as s kk ! j"
    using SubsetSum_Padded_Enc.bits_roundtrip SubsetSum_Padded_Enc_axioms v_in 
    by blast
  show ?thesis
    by (simp add: Lval_at_def slice round)
qed

lemma Good_char_encR:
  "Good as s oL ((!) (x0 as s))
   \<longleftrightarrow> (\<exists>jL<length (enumL as s kk). Lval_at as s oL jL \<in> set (enumR as s kk))"
proof
  (* \<Rightarrow> *)
  assume H: "Good as s oL ((!) (x0 as s))"
  then obtain jL jR where
    jL: "jL < length (enumL as s kk)" and jR: "jR < length (enumR as s kk)" and
    eq: "Lval_at as s oL jL = Rval_at as s ((!) (x0 as s)) jR"
    unfolding Good_def good_def by blast
  hence "Lval_at as s oL jL = enumR as s kk ! jR"
    by (simp add: Rval_at_on_enc_block jR)
  thus "\<exists>jL<length (enumL as s kk). Lval_at as s oL jL \<in> set (enumR as s kk)"
    using jL in_set_conv_nth by (metis jR)
next
  (* \<Leftarrow> *)
  assume "\<exists>jL<length (enumL as s kk). Lval_at as s oL jL \<in> set (enumR as s kk)"
  then obtain jL where jL: "jL < length (enumL as s kk)"
    and mem: "Lval_at as s oL jL \<in> set (enumR as s kk)" by blast
  then obtain jR where jR: "jR < length (enumR as s kk)"
    and eq0: "enumR as s kk ! jR = Lval_at as s oL jL"
    using in_set_conv_nth by metis
  hence "Rval_at as s ((!) (x0 as s)) jR = Lval_at as s oL jL"
    by (simp add: Rval_at_on_enc_block jR)
  thus "Good as s oL ((!) (x0 as s))"
    using jL jR Good_def good_def by metis
qed

lemma flipL0:
  assumes jL: "j < length (enumL as s kk)"
      and L2: "2 \<le> length (enumL as s kk)"
      and hit:  "\<exists>v\<in>set (enumL as s kk). v \<in> set (enumR as s kk)"
      and miss: "\<exists>v\<in>set (enumL as s kk). v \<notin> set (enumR as s kk)"
      and baseline_only_j:
        "Good as s ((!) (x0 as s)) ((!) (x0 as s)) \<longrightarrow>
        (\<forall>j'<length (enumL as s kk). j' \<noteq> j \<longrightarrow>
        Lval_at as s ((!) (x0 as s)) j' \<notin> set (enumR as s kk))"
  shows "\<exists>oL'.
           (\<forall>i. i \<notin> blockL_abs enc0 as s j \<longrightarrow> oL' i = ((!) (enc as s kk)) i)
         \<and> Good as s oL' ((!) (enc as s kk))
           \<noteq> Good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
proof -
  let ?a = "length (enc0 as s) + offL as s j"
  let ?w = "W as s"
  (* pick two distinct L-catalog values to write *)
  have lt0: "0 < length (enumL as s kk)" and lt1: "1 < length (enumL as s kk)"
    using L2 by auto
  define p where "p = enumL as s kk ! 0"
  define q where "q = enumL as s kk ! 1"
  have p_in: "p \<in> set (enumL as s kk)"
    unfolding p_def by (rule nth_mem) (use lt0 in simp)
  have q_in: "q \<in> set (enumL as s kk)"
    unfolding q_def by (rule nth_mem) (use lt1 in simp)
  obtain bp where bp_len: "length bp = ?w" and bp_val: "from_bits bp = p"
    using p_in bits_roundtrip by blast
  obtain bq where bq_len: "length bq = ?w" and bq_val: "from_bits bq = q"
    using q_in bits_roundtrip by blast

  (* two candidate left-oracles that overwrite only block j *)
  define oL_p where
    "oL_p i = (if i \<in> blockL_abs enc0 as s j then bp ! (i - ?a)
               else (enc as s kk) ! i)" for i
  define oL_q where
    "oL_q i = (if i \<in> blockL_abs enc0 as s j then bq ! (i - ?a)
               else (enc as s kk) ! i)" for i
  have blk_eq: "blockL_abs enc0 as s j = {?a ..< ?a + ?w}"
    by (simp add: blockL_abs_def offL_def)

  have Lval_p: "Lval_at as s oL_p j = p"
  proof -
    have slice: "map oL_p [?a ..< ?a + ?w] = bp"
    proof (rule nth_equalityI)
      show "length (map oL_p [?a ..< ?a + ?w]) = length bp"
        by (simp add: bp_len)
    next
      fix t assume "t < length (map oL_p [?a ..< ?a + ?w])"
      hence tw: "t < ?w" by simp
      have idx: "[?a ..< ?a + ?w] ! t = ?a + t" using tw by simp
      have inblk: "?a + t \<in> blockL_abs enc0 as s j"
        using tw by (simp add: blk_eq)
      show "map oL_p [?a ..< ?a + ?w] ! t = bp ! t"
        using nth_map idx oL_p_def inblk by (simp add: tw)
    qed
    show ?thesis
      by (simp add: Lval_at_def slice bp_val)
  qed

  have Lval_q: "Lval_at as s oL_q j = q"
  proof -
    have slice: "map oL_q [?a ..< ?a + ?w] = bq"
    proof (rule nth_equalityI)
      show "length (map oL_q [?a ..< ?a + ?w]) = length bq"
        by (simp add: bq_len)
    next
      fix t assume "t < length (map oL_q [?a ..< ?a + ?w])"
      hence tw: "t < ?w" by simp
      have idx: "[?a ..< ?a + ?w] ! t = ?a + t" using tw by simp
      have inblk: "?a + t \<in> blockL_abs enc0 as s j"
        using tw by (simp add: blk_eq)
      show "map oL_q [?a ..< ?a + ?w] ! t = bq ! t"
        using nth_map idx oL_q_def inblk by (simp add: tw)
    qed
    show ?thesis
      by (simp add: Lval_at_def slice bq_val)
  qed

  have outside_p:
    "\<forall>i. i \<notin> blockL_abs enc0 as s j \<longrightarrow> oL_p i = (enc as s kk) ! i"
    by (simp add: oL_p_def)
  have outside_q:
    "\<forall>i. i \<notin> blockL_abs enc0 as s j \<longrightarrow> oL_q i = (enc as s kk) ! i"
    by (simp add: oL_q_def)

  (* Decide which one flips relative to the baseline *)
  show ?thesis
  proof (cases "Good as s (\<lambda>i. (enc as s kk) ! i) (\<lambda>i. (enc as s kk) ! i)")
    case True
    (* Baseline is good \<rightarrow> pick an L-value outside set(enumR) to force \<not>Good *)
    from miss obtain v_out where v_outL: "v_out \<in> set (enumL as s kk)"
      and v_outNR: "v_out \<notin> set (enumR as s kk)" by blast
    then obtain v_out where v_outL: "v_out \<in> set (enumL as s kk)"
      and v_outNR: "v_out \<notin> set (enumR as s kk)" by blast
    obtain bv where bv_len: "length bv = ?w" and bv_val: "from_bits bv = v_out"
      using v_outL bits_roundtrip by blast
    define oL_out where
      "oL_out i = (if i \<in> blockL_abs enc0 as s j then bv ! (i - ?a)
                   else (enc as s kk) ! i)" for i
    have Lval_out: "Lval_at as s oL_out j = v_out"
    proof -
      let ?a = "length (enc0 as s) + offL as s j"
      let ?w = "W as s"
      have blk_eq: "blockL_abs enc0 as s j = {?a ..< ?a + ?w}"
        by (simp add: blockL_abs_def offL_def)

      have slice: "map oL_out [?a ..< ?a + ?w] = bv"
      proof (rule nth_equalityI)
        show "length (map oL_out [?a ..< ?a + ?w]) = length bv"
          by (simp add: bv_len)
      next
        fix t assume "t < length (map oL_out [?a ..< ?a + ?w])"
        hence tw: "t < ?w" by simp
        have idx: "[?a ..< ?a + ?w] ! t = ?a + t" using tw by simp
        have inblk: "?a + t \<in> blockL_abs enc0 as s j"
          using tw by (simp add: blk_eq)
        show "map oL_out [?a ..< ?a + ?w] ! t = bv ! t"
          using nth_map idx oL_out_def inblk by (simp add: tw)
      qed

      show ?thesis
        by (simp add: Lval_at_def slice bv_val)
    qed

    have same_block:
      "\<And>j'. j' \<noteq> j \<Longrightarrow> Lval_at as s oL_out j' = Lval_at as s ((!) (x0 as s)) j'"
    proof -
      fix j' assume ne: "j' \<noteq> j"
      let ?a' = "length (enc0 as s) + offL as s j'"
      let ?w' = "W as s"
      have blk': "blockL_abs enc0 as s j' = {?a' ..< ?a' + ?w'}"
        by (simp add: blockL_abs_def offL_def)
      have slice_eq:
        "map oL_out [?a' ..< ?a' + ?w'] =
         map ((!) (x0 as s)) [?a' ..< ?a' + ?w']"
      proof (rule nth_equalityI)
        show "length (map oL_out [?a' ..< ?a' + ?w'])
              = length (map ((!) (x0 as s)) [?a' ..< ?a' + ?w'])" by simp
      next
        fix t assume "t < length (map oL_out [?a' ..< ?a' + ?w'])"
        hence tw: "t < ?w'" by simp
        have idx: "[?a' ..< ?a' + ?w'] ! t = ?a' + t" using tw by simp
        have in_j': "?a' + t \<in> blockL_abs enc0 as s j'" using tw by (simp add: blk')
        have not_in_j: "?a' + t \<notin> blockL_abs enc0 as s j"
          using blockL_abs_disjoint[OF ne] in_j' by auto
        have out_eq: "oL_out (?a' + t) = (x0 as s) ! (?a' + t)"
          by (simp add: oL_out_def not_in_j)
        show "map oL_out [?a' ..< ?a' + ?w'] ! t
              = map ((!) (x0 as s)) [?a' ..< ?a' + ?w'] ! t"
          using nth_map idx out_eq by (simp add: tw)
      qed
      show "Lval_at as s oL_out j' = Lval_at as s ((!) (x0 as s)) j'"
        by (simp add: Lval_at_def slice_eq)
    qed
     (* Good characterization specialized to oL_out *)
    have Good_char_oL_out:
      "Good as s oL_out ((!) (x0 as s))
       \<longleftrightarrow> (\<exists>jL<length (enumL as s kk). Lval_at as s oL_out jL \<in> set (enumR as s kk))"
      by (rule Good_char_encR)

    (* no jL witnesses after the overwrite \<Rightarrow> \<not>Good *)
    have not_good_out: "\<not> Good as s oL_out ((!) (x0 as s))"
    proof -
      have none:
        "\<And>j'. j' < length (enumL as s kk) \<Longrightarrow>
          Lval_at as s oL_out j' \<notin> set (enumR as s kk)"
      proof -
        fix j' assume j'lt: "j' < length (enumL as s kk)"
        show "Lval_at as s oL_out j' \<notin> set (enumR as s kk)"
        proof (cases "j' = j")
          case True
          have "Lval_at as s oL_out j' = v_out"
            using True by (simp add: Lval_out)
          thus ?thesis using v_outNR by simp
        next
          case False
          have "Lval_at as s oL_out j' = Lval_at as s ((!) (x0 as s)) j'"
            by (rule same_block[OF False])
          also have "... \<notin> set (enumR as s kk)"
            using baseline_only_j \<open>Good as s ((!) (x0 as s)) ((!) (x0 as s))\<close> j'lt False by blast
          finally show ?thesis .
        qed
      qed
      thus ?thesis by (simp only: Good_char_oL_out) blast
    qed

    have outside_out: "\<forall>i. i \<notin> blockL_abs enc0 as s j \<longrightarrow> oL_out i = (x0 as s) ! i"
      by (simp add: oL_out_def)
    show ?thesis
      by (intro exI[of _ oL_out]) (use outside_out True not_good_out in auto)

  next
    case False
    (* Baseline is NOT good \<rightarrow> choose an L-value that *is* in enumR to force Good *)
    from hit obtain v_in where v_inL: "v_in \<in> set (enumL as s kk)"
      and v_inR: "v_in \<in> set (enumR as s kk)" by blast
    obtain bv where bv_len: "length bv = ?w" and bv_val: "from_bits bv = v_in"
      using v_inL bits_roundtrip by blast

    define oL_in where
      "oL_in i = (if i \<in> blockL_abs enc0 as s j then bv ! (i - ?a)
                  else (x0 as s) ! i)" for i

    have blk_eq': "blockL_abs enc0 as s j = {?a ..< ?a + ?w}"
      by (simp add: blockL_abs_def offL_def)

    have slice: "map oL_in [?a ..< ?a + ?w] = bv"
    proof (rule nth_equalityI)
      show "length (map oL_in [?a ..< ?a + ?w]) = length bv" by (simp add: bv_len)
    next
      fix t assume "t < length (map oL_in [?a ..< ?a + ?w])"
      hence tw: "t < ?w" by simp
      have idx: "[?a ..< ?a + ?w] ! t = ?a + t" using tw by simp
      have inblk: "?a + t \<in> blockL_abs enc0 as s j" using tw by (simp add: blk_eq')
      show "map oL_in [?a ..< ?a + ?w] ! t = bv ! t"
        using nth_map idx oL_in_def inblk by (simp add: tw)
    qed

    have Lval_in: "Lval_at as s oL_in j = v_in"
      by (simp add: Lval_at_def slice bv_val)

    have good_in: "Good as s oL_in ((!) (x0 as s))"
      using Good_char_encR Lval_in v_inR jL by auto

    have outside_in: "\<forall>i. i \<notin> blockL_abs enc0 as s j \<longrightarrow> oL_in i = (x0 as s) ! i"
      by (simp add: oL_in_def)

    show ?thesis
      by (intro exI[of _ oL_in]) (use outside_in False good_in in auto)
  qed
qed

lemma flipR0:
  assumes "j < length (enumR as s kk)" "2 \<le> length (enumR as s kk)"
  shows "\<exists>oR'. (\<forall>i. i \<notin> blockR_abs enc0 as s kk j \<longrightarrow> oR' i = oR i)
             \<and> Rval_at as s oR' j \<noteq> Rval_at as s oR j"
  using flipR_pointwise_block[OF assms] by blast

(* coverage for the concrete input x0, using the block-flip lemmas *)
lemma coverage_for_enc_blocks:
  assumes L2: "2 \<le> length (enumL as s kk)"
      and R2: "2 \<le> length (enumR as s kk)"
      and hit:
        "\<exists>v\<in>set (enumL as s kk). v \<in> set (enumR as s kk)"
      and miss:
        "\<exists>v\<in>set (enumL as s kk). v \<notin> set (enumR as s kk)"
      and baseline_only_j:
        "\<And>j. Good as s ((!) (enc as s kk)) ((!) (enc as s kk)) \<longrightarrow>
             (\<forall>j'<length (enumL as s kk). j' \<noteq> j \<longrightarrow>
                Lval_at as s ((!) (enc as s kk)) j' \<notin> set (enumR as s kk))"
  shows
    "(\<forall>j<length (enumL as s kk). touches (enc as s kk) (blockL_abs enc0 as s j)) \<and>
     (\<forall>j<length (enumR as s kk). touches (enc as s kk) (blockR_abs enc0 as s kk j))"
proof (intro conjI allI impI)
  define x where [simp]: "x = enc as s kk"

  fix j assume jL: "j < length (enumL as s kk)"
  {
    assume not_touch: "Base.read0 M x \<inter> blockL_abs enc0 as s j = {}"

    from flipL0[OF jL L2 hit miss baseline_only_j]
    obtain oL' where
      outside_enc: "\<And>i. i \<notin> blockL_abs enc0 as s j \<Longrightarrow> oL' i = ((enc as s kk) ! i)" and
      neq: "Good as s oL' ((!) (enc as s kk))
        \<noteq> Good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
      by blast

(* THEN: immediately rewrite to your local abbreviation x = enc as s kk *)
    have outside: "\<And>i. i \<notin> blockL_abs enc0 as s j \<Longrightarrow> oL' i = x ! i"
      using outside_enc by (simp)  (* uses [simp] rewrite of x = enc as s kk *)

(* Turn \<noteq> into = (\<not> \<dots>) so we can feed it to the continuation *)
    have flip_neg:
      "Good as s oL' ((!) (x0 as s)) =
      (\<not> Good as s ((!) (x0 as s)) ((!) (x0 as s)))"
      using neq by (cases "Good as s ((!) (x0 as s)) ((!) (x0 as s))") auto

(* On booleans, p \<noteq> q  \<Longrightarrow>  p = \<not>q *)
    have flip_as_eq:
      "Good as s oL' ((!) x) = (\<not> Good as s ((!) x) ((!) x))"
      using neq by (cases "Good as s ((!) x) ((!) x)") auto

    have flip_neg:
      "Good as s oL' ((!) x) = (\<not> Good as s ((!) x) ((!) x))"
      using neq by (cases "Good as s ((!) x) ((!) x)") auto

    define a where "a = length (enc0 as s) + offL as s j"
    define w where "w = W as s"

    have BND: "a + w \<le> length (enc as s kk)"
      using offL_window_in_enc[OF jL] unfolding a_def w_def by simp
    have ALE: "a \<le> length (enc as s kk)" using BND by linarith
    have LEN: "length (map oL' [a ..< a + w]) = w" by simp

    define y where "y = splice a w (enc as s kk) (map oL' [a ..< a + w])"

    (* Outside the block, y agrees with x *)
    have agree_unread: "\<And>i. i \<in> Base.read0 M x \<Longrightarrow> x ! i = y ! i"
    proof -
      fix i assume iR: "i \<in> Base.read0 M x"
      from not_touch iR have i_not_blk: "i \<notin> blockL_abs enc0 as s j" by auto
      have blk: "blockL_abs enc0 as s j = {a ..< a + w}"
        by (simp add: a_def w_def blockL_abs_def offL_def)
      have not_in: "i \<notin> {a ..< a + w}"
        using i_not_blk blk by simp
      have disj: "i < a \<or> a + w \<le> i"
        using not_in atLeastLessThan_iff by auto
      from disj show "x ! i = y ! i"
        by (elim disjE; simp add: y_def splice_nth_left ALE splice_nth_right LEN BND)
    qed

    have acc_same: "accepts M x \<longleftrightarrow> accepts M y"
      by (rule unread_agreement) (use agree_unread in blast)

    (* On the block, y equals oL' pointwise *)
    have y_eq_oL'_onblock: "\<And>i. i \<in> {a ..< a + w} \<Longrightarrow> y ! i = oL' i"
    proof -
      fix i assume inB: "i \<in> {a ..< a + w}"
      then have ai: "a \<le> i" and ilt: "i < a + w" by auto
      have "y ! i = (map oL' [a ..< a + w]) ! (i - a)"
        by (simp add: y_def splice_nth_inside[OF LEN BND ai ilt])
      also have "... = oL' ([a ..< a + w] ! (i - a))"
        using nth_map ai ilt by auto
      also have "... = oL' i" using ai ilt by simp
      finally show "y ! i = oL' i" .
    qed

(* Turn block equality + outside premise into global equality *)
    have oL'_eq_y_all: "\<And>i. y ! i = oL' i"
    proof -
      fix i
      have blk: "blockL_abs enc0 as s j = {a ..< a + w}"
        by (simp add: a_def w_def blockL_abs_def offL_def)
      consider (IN) "i \<in> {a ..< a + w}" | (OUT) "i \<notin> {a ..< a + w}" by blast
      then show "y ! i = oL' i"
      proof cases
        case IN  show ?thesis by (rule y_eq_oL'_onblock[OF IN])
      next
        case OUT
        hence "y ! i = x ! i"
          by (cases "i < a")
            (simp_all add: y_def splice_nth_left ALE splice_nth_right LEN BND)
        moreover from OUT blk have "oL' i = x ! i" by (simp add: outside)
        ultimately show ?thesis by simp
      qed
    qed

    (* Tie to run/Good and contradict unread-agreement *)
    have run_x:
      "run (\<lambda>i. x ! i) (\<lambda>i. x ! i) (T0 as s) = Good as s (\<lambda>i. x ! i) (\<lambda>i. x ! i)"
      by (simp add: correct_T0)
    have run_y_eq_run_x:
      "run (\<lambda>i. y ! i) (\<lambda>i. x ! i) (T0 as s) = run (\<lambda>i. x ! i) (\<lambda>i. x ! i) (T0 as s)"
    proof (rule run_agrees_on_seen)
      (* seenL indices are within read0, where y equals x *)
      fix i assume "i \<in> seenL_run ((!) y) ((!) x) (T0 as s)"
      hence "i \<in> Base.read0 M x" by (meson correctness)
      thus "y ! i = x ! i" using agree_unread by blast
    next
      (* seenR indices are within read0 as well, but our right oracle is already ?x *)
      fix j assume "j \<in> seenR_run ((!) y) ((!) x) (T0 as s)"
      thus "(x ! j) = (x ! j)" by simp
    qed

    have Good_flip_inputs:
      "Good as s (\<lambda>i. y ! i) (\<lambda>i. x ! i) \<noteq> Good as s (\<lambda>i. x ! i) (\<lambda>i. x ! i)"
      using neq oL'_eq_y_all by auto

    have run_diff:
      "run (\<lambda>i. y ! i) (\<lambda>i. x ! i) (T0 as s) \<noteq> run (\<lambda>i. x ! i) (\<lambda>i. x ! i) (T0 as s)"
      using Good_flip_inputs run_x run_y_eq_run_x
      by (meson correctness)

    have acc_x:
      "run (\<lambda>i. x ! i) (\<lambda>i. x ! i) (T0 as s) = accepts M x"
      using run_diff run_y_eq_run_x by blast
    have acc_y':
      "run (\<lambda>i. y ! i) (\<lambda>i. x ! i) (T0 as s) = accepts M y"
      using run_diff run_y_eq_run_x by blast

    from acc_same acc_x acc_y' run_diff have False by simp
  }
  then have "Base.read0 M x \<inter> blockL_abs enc0 as s j \<noteq> {}" by blast
  thus "touches (enc as s kk) (blockL_abs enc0 as s j)"
    unfolding touches_def x_def by simp
next
(* ---------------- R blocks (symmetric) ---------------- *)
  fix j assume jR: "j < length (enumR as s kk)"
  {
    assume not_touch: "Base.read0 M x \<inter> blockR_abs enc0 as s kk j = {}"

(* pick u from the catalog *)
    obtain oR' where
      oR'_outside: "\<And>i. i \<notin> blockR_abs enc0 as s kk j \<Longrightarrow> oR' i = (\<lambda>i. x ! i) i" and
      Rval_flip:   "Rval_at as s oR' j \<noteq> Rval_at as s (\<lambda>i. x ! i) j"
      using flipR0[OF jR R2] by blast

    define a where "a = length (enc0 as s) + offR as s kk j"
    define w where "w = W as s"

    have BND: "a + w \<le> length (enc as s kk)"
      using offR_window_in_enc[OF jR] unfolding a_def w_def by simp
    have ALE: "a \<le> length (enc as s kk)" using BND by linarith
    have LEN: "length (map oR' [a ..< a + w]) = w" by simp

    define y where "y = splice a w (enc as s kk) (map oR' [a ..< a + w])"

 (* Outside the block, y agrees with x *)
    have agree_unread: "\<And>i. i \<in> Base.read0 M x \<Longrightarrow> x ! i = y ! i"
    proof -
      fix i assume iR: "i \<in> Base.read0 M x"
      have i_not_blk: "i \<notin> blockR_abs enc0 as s kk j" using not_touch iR by auto
      have blk: "blockR_abs enc0 as s kk j = {a ..< a + w}"
        by (simp add: a_def w_def blockR_abs_def offR_def length_padL)
      from i_not_blk blk have disj:"i < a \<or> a + w \<le> i" using atLeastLessThan_iff by auto
      from disj show "x ! i = y ! i"
      proof
        assume "i < a"
        with ALE show ?thesis
          unfolding y_def splice_nth_left by (meson correctness)
      next
        assume "a + w \<le> i"
        with LEN BND show ?thesis
          unfolding y_def splice_nth_left by (meson correctness)
      qed
    qed

(* unread-agreement *)
    have acc_same: "accepts M x \<longleftrightarrow> accepts M y"
      by (rule unread_agreement) (use agree_unread in blast)

 (* On the block, y equals oR' pointwise *)
    have y_eq_oR'_onblock: "\<And>i. i \<in> {a ..< a + w} \<Longrightarrow> y ! i = oR' i"
    proof -
      fix i assume inB: "i \<in> {a ..< a + w}"
      then have ai: "a \<le> i" and ilt: "i < a + w" by auto
      have "y ! i = (map oR' [a ..< a + w]) ! (i - a)"
        by (simp add: y_def splice_nth_inside[OF LEN BND ai ilt])
      also have "... = oR' ([a ..< a + w] ! (i - a))" using ai ilt by force
      also have "... = oR' i" using ai ilt by simp
      finally show "y ! i = oR' i" .
    qed

    (* Turn block equality + oR'_outside into global equality *)
    have oR'_eq_y_all: "\<And>i. y ! i = oR' i"
    proof -
      fix i
      have blk: "blockR_abs enc0 as s kk j = {a ..< a + w}"
        by (simp add: a_def w_def blockR_abs_def offR_def length_padL)
      consider (IN) "i \<in> {a ..< a + w}" | (OUT) "i \<notin> {a ..< a + w}" by blast
      then show "y ! i = oR' i"
      proof cases
        case IN  show ?thesis by (rule y_eq_oR'_onblock[OF IN])
      next
        case OUT
        have yi_eq_xi: "y ! i = x ! i"
        proof (cases "i < a")
          case True
          with ALE show ?thesis
            unfolding y_def splice_nth_left by (meson correctness)
        next
          case False
          from OUT blk have "a + w \<le> i"
            using atLeastLessThan_iff False by auto
          with LEN BND show ?thesis
            unfolding y_def splice_nth_left by (meson correctness)
        qed
        moreover from OUT blk have "oR' i = x ! i"
          by (simp add: oR'_outside)
        ultimately show "y ! i = oR' i" by simp
      qed
    qed

    (* Correctness of the machine on x and on (x,y) *)
    have run_x:
      "run (\<lambda>i. x ! i) (\<lambda>i. x ! i) (T0 as s) = Good as s (\<lambda>i. x ! i) (\<lambda>i. x ! i)"
      by (meson correctness)
    have run_y:
      "run (\<lambda>i. x ! i) (\<lambda>i. y ! i) (T0 as s) = Good as s (\<lambda>i. x ! i) (\<lambda>i. y ! i)"
      by (meson correctness)

    (* The R-value at j changed when we switch to y *)
    have Rval_changed: "Rval_at as s (\<lambda>i. y ! i) j \<noteq> Rval_at as s (\<lambda>i. x ! i) j"
      by (simp add: oR'_eq_y_all Rval_flip)

    (* Hence the runs differ *)
    have run_diff:
      "run (\<lambda>i. x ! i) (\<lambda>i. y ! i) (T0 as s)
       \<noteq> run (\<lambda>i. x ! i) (\<lambda>i. x ! i) (T0 as s)"
      using run_x run_y Rval_changed by (meson correctness)

    (* But unread-agreement would force equal acceptance — contradiction *)
    have acc_x:
      "run (\<lambda>i. x ! i) (\<lambda>i. x ! i) (T0 as s) = accepts M x"
      using correct_T0 accepts_sem tm_to_dtr_accepts[simplified T0_def T_def] by (meson correctness)
    have acc_y':
      "run (\<lambda>i. x ! i) (\<lambda>i. y ! i) (T0 as s) = accepts M y"
      using correct_T0 accepts_sem tm_to_dtr_accepts[simplified T0_def T_def] by (meson correctness)
    from acc_same acc_x acc_y' run_diff have False by simp
  }
  then have "Base.read0 M x \<inter> blockR_abs enc0 as s kk j \<noteq> {}" by blast
  thus "touches (enc as s kk) (blockR_abs enc0 as s kk j)"
    by (meson correctness)
qed

(* 9) The coverage result you wanted, phrased on block families *)
lemma coverage_blocks:
  assumes "n = length as" "distinct_subset_sums as"
  shows
   "(\<forall>j<length (enumL as s kk). touches (enc as s kk) (blockL_abs enc0 as s j)) \<and>
   (\<forall>j<length (enumR as s kk). touches (enc as s kk) (blockR_abs enc0 as s kk j))"
proof (intro conjI allI impI)
  define x where [simp]: "x = enc as s kk"
  fix j assume jL: "j < length (enumL as s kk)"
  obtain i where "i \<in> Base.read0 M x" "i \<in> blockL_abs enc0 as s j"
    by (meson correctness)
  thus "touches x (blockL_abs enc0 as s j)" using touches_def by blast
next
  define x where [simp]: "x = enc as s kk"
  fix j assume jR: "j < length (enumR as s kk)"
  obtain i where "i \<in> Base.read0 M x" "i \<in> blockR_abs enc0 as s kk j"
    by (meson correctness)
  thus "touches x (blockR_abs enc0 as s kk j)" using touches_def by blast
qed

lemma steps_lower_bound:
  assumes n_def: "n = length as" and distinct: "distinct_subset_sums as"
  shows "steps M (enc as s kk) \<ge>
           card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n)"
proof -
  from coverage_blocks[OF n_def distinct] obtain
    Lcov_ALL: "\<forall>j<length (enumL as s kk). touches (enc as s kk) (blockL_abs enc0 as s j)" and
    Rcov_ALL: "\<forall>j<length (enumR as s kk). touches (enc as s kk) (blockR_abs enc0 as s kk j)"
    by blast

  have Lcov:
    "\<And>j. j < length (enumL as s kk) \<Longrightarrow> touches (enc as s kk) (blockL_abs enc0 as s j)"
    using Lcov_ALL by auto
  have Rcov:
    "\<And>j. j < length (enumR as s kk) \<Longrightarrow> touches (enc as s kk) (blockR_abs enc0 as s kk j)"
    using Rcov_ALL by auto

  define x0 where "x0 = enc as s kk"
  define R0 :: "nat set" where "R0 = Base.read0 M x0"

  define IL where "IL = {0..<length (enumL as s kk)}"
  define IR where "IR = {0..<length (enumR as s kk)}"

  (* pick one read index from each touched absolute block *)
  define pickL where "pickL j = (SOME i. i \<in> R0 \<and> i \<in> blockL_abs enc0 as s j)" for j
  define pickR where "pickR j = (SOME i. i \<in> R0 \<and> i \<in> blockR_abs enc0 as s kk j)" for j

 (* existence: each touched block contributes one read index *)
  have exL:
    "\<And>j. j \<in> IL \<Longrightarrow> \<exists>i. i \<in> R0 \<and> i \<in> blockL_abs enc0 as s j"
  proof -
    fix j assume jIL: "j \<in> IL"
    have jlt: "j < length (enumL as s kk)" using IL_def jIL by simp
    from Lcov[OF jlt] obtain i where
      i1: "i \<in> Base.read0 M x0" and i2: "i \<in> blockL_abs enc0 as s j"
      using touches_def by (meson correctness)
    show "\<exists>i. i \<in> R0 \<and> i \<in> blockL_abs enc0 as s j"
      by (intro exI[of _ i]) (simp add: R0_def i1 i2)
  qed

  have exR:
    "\<And>j. j \<in> IR \<Longrightarrow> \<exists>i. i \<in> R0 \<and> i \<in> blockR_abs enc0 as s kk j"
  proof -
    fix j assume jIR: "j \<in> IR"
    have jlt: "j < length (enumR as s kk)" using IR_def jIR by simp
    from Rcov[OF jlt] obtain i where
      i1: "i \<in> Base.read0 M x0" and i2: "i \<in> blockR_abs enc0 as s kk j"
      using touches_def by (meson correctness)
    show "\<exists>i. i \<in> R0 \<and> i \<in> blockR_abs enc0 as s kk j"
      by (intro exI[of _ i]) (simp add: R0_def i1 i2)
  qed

  (* witnesses belong to R0 and their blocks *)
  have pickL_in:
    "\<And>j. j \<in> IL \<Longrightarrow> pickL j \<in> R0 \<and> pickL j \<in> blockL_abs enc0 as s j"
  proof -
    fix j assume jIL: "j \<in> IL"
    from exL[OF jIL]
    show "pickL j \<in> R0 \<and> pickL j \<in> blockL_abs enc0 as s j"
      unfolding pickL_def by (rule someI_ex)
  qed

  have pickR_in:
    "\<And>j. j \<in> IR \<Longrightarrow> pickR j \<in> R0 \<and> pickR j \<in> blockR_abs enc0 as s kk j"
  proof -
    fix j assume jIR: "j \<in> IR"
    from exR[OF jIR]
    show "pickR j \<in> R0 \<and> pickR j \<in> blockR_abs enc0 as s kk j"
      unfolding pickR_def by (rule someI_ex)
  qed

  (* images are subsets of R0 *)
  have subL: "pickL ` IL \<subseteq> R0"
  proof
    fix i assume "i \<in> pickL ` IL"
    then obtain j where jIL: "j \<in> IL" and i_eq: "i = pickL j" by auto
    from pickL_in[OF jIL] have "pickL j \<in> R0" by blast
    thus "i \<in> R0" by (simp add: i_eq)
  qed

  have subR: "pickR ` IR \<subseteq> R0"
  proof
    fix i assume "i \<in> pickR ` IR"
    then obtain j where jIR: "j \<in> IR" and i_eq: "i = pickR j" by auto
    from pickR_in[OF jIR] have "pickR j \<in> R0" by blast
    thus "i \<in> R0" by (simp add: i_eq)
  qed

  have union_sub: "pickL ` IL \<union> pickR ` IR \<subseteq> R0"
    using subL subR by auto

  (* injectivity inside L and inside R, by disjoint absolute blocks *)
  have injL: "inj_on pickL IL"
  proof (rule inj_onI)
    fix j1 j2 assume j1: "j1 \<in> IL" and j2: "j2 \<in> IL" and eq: "pickL j1 = pickL j2"
    obtain i1 where i1: "i1 \<in> R0 \<and> i1 \<in> blockL_abs enc0 as s j1" using exL[OF j1] by blast
    obtain i2 where i2: "i2 \<in> R0 \<and> i2 \<in> blockL_abs enc0 as s j2" using exL[OF j2] by blast
    have in1: "pickL j1 \<in> blockL_abs enc0 as s j1"
      using \<open>pickL \<equiv> \<lambda>j. SOME i. i \<in> R0 \<and> i \<in> blockL_abs enc0 as s j\<close> j1 pickL_in by auto
    have in2: "pickL j2 \<in> blockL_abs enc0 as s j2"
      using \<open>pickL \<equiv> \<lambda>j. SOME i. i \<in> R0 \<and> i \<in> blockL_abs enc0 as s j\<close> j2 pickL_in by auto
    have inter_nonempty:
      "blockL_abs enc0 as s j1 \<inter> blockL_abs enc0 as s j2 \<noteq> {}"
      using eq in1 in2 by auto
    show "j1 = j2"
    proof (rule ccontr)
      assume "j1 \<noteq> j2"
      hence "blockL_abs enc0 as s j1 \<inter> blockL_abs enc0 as s j2 = {}"
        by (rule blockL_abs_disjoint)
      with inter_nonempty show False by contradiction
    qed
  qed

  have injR: "inj_on pickR IR"
  proof (rule inj_onI)
    fix j1 j2 assume j1: "j1 \<in> IR" and j2: "j2 \<in> IR" and eq: "pickR j1 = pickR j2"
    obtain i1 where i1: "i1 \<in> R0 \<and> i1 \<in> blockR_abs enc0 as s kk j1" using exR[OF j1] by blast
    obtain i2 where i2: "i2 \<in> R0 \<and> i2 \<in> blockR_abs enc0 as s kk j2" using exR[OF j2] by blast
    have in1: "pickR j1 \<in> blockR_abs enc0 as s kk j1"
      using \<open>pickR \<equiv> \<lambda>j. SOME i. i \<in> R0 \<and> i \<in> blockR_abs enc0 as s kk j\<close> j1 pickR_in by blast
    have in2: "pickR j2 \<in> blockR_abs enc0 as s kk j2"
      using \<open>pickR \<equiv> \<lambda>j. SOME i. i \<in> R0 \<and> i \<in> blockR_abs enc0 as s kk j\<close> j2 pickR_in by blast
    have inter_nonempty:
      "blockR_abs enc0 as s kk j1 \<inter> blockR_abs enc0 as s kk j2 \<noteq> {}"
      using eq in1 in2 by auto
    show "j1 = j2"
    proof (rule ccontr)
      assume "j1 \<noteq> j2"
      hence "blockR_abs enc0 as s kk j1 \<inter> blockR_abs enc0 as s kk j2 = {}"
        by (rule blockR_abs_disjoint)
      with inter_nonempty show False by contradiction
    qed
  qed

  (* images are disjoint across L and R *)
  have disj_images: "(pickL ` IL) \<inter> (pickR ` IR) = {}"
  proof
    show "(pickL ` IL) \<inter> (pickR ` IR) \<subseteq> {}"
    proof
      fix i assume iin: "i \<in> (pickL ` IL) \<inter> (pickR ` IR)"
      then obtain jL where jL: "jL \<in> IL" and iL: "i = pickL jL" by blast
      from iin obtain jR where jR: "jR \<in> IR" and iR: "i = pickR jR" by blast
      have inL: "i \<in> blockL_abs enc0 as s jL"
        using iL pickL_in[OF jL] by auto
      have inR: "i \<in> blockR_abs enc0 as s kk jR"
        using iR pickR_in[OF jR] by auto
      have jL_lt: "jL < length (enumL as s kk)" using IL_def jL by auto
      have disj: "blockL_abs enc0 as s jL \<inter> blockR_abs enc0 as s kk jR = {}"
        by (rule blockL_abs_blockR_abs_disjoint[OF jL_lt])
      from inL inR disj show "i \<in> {}" by auto
    qed
  qed simp

  (* count *)
  have fin_R0: "finite R0" using R0_def by simp
  have fin_imgL: "finite (pickL ` IL)" by (intro finite_imageI) (simp add: IL_def)
  have fin_imgR: "finite (pickR ` IR)" by (intro finite_imageI) (simp add: IR_def)

  have card_lower: "card (pickL ` IL \<union> pickR ` IR) \<le> card R0"
    by (rule card_mono[OF fin_R0 union_sub])

  have card_union:
    "card (pickL ` IL \<union> pickR ` IR) = card (pickL ` IL) + card (pickR ` IR)"
    by (subst card_Un_disjoint) (use disj_images fin_imgL fin_imgR in auto)

  have inj_cardL: "card (pickL ` IL) = card IL" by (rule card_image[OF injL])
  have inj_cardR: "card (pickR ` IR) = card IR" by (rule card_image[OF injR])

  from card_lower card_union inj_cardL inj_cardR
  have A: "card IL + card IR \<le> card R0" by simp

  have card_IL: "card IL = card (LHS (e_k as s kk) n)"
    by (simp add: IL_def enumL_def n_def)
  have card_IR: "card IR = card (RHS (e_k as s kk) n)"
    by (simp add: IR_def enumR_def n_def)

  have B:
   "card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n) \<le> card R0"
    using A by (simp add: card_IL card_IR)

  (* final sandwich with steps *)
  have "card R0 \<le> steps M x0"
    by (simp add: R0_def Base.card_read0_le_steps)
  from B this have "card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n) \<le> steps M x0"
    by (rule le_trans)
  thus ?thesis by (simp add: x0_def)
qed

end  (* context Coverage_TM *)

end  (* theory *)