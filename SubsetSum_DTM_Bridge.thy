theory SubsetSum_DTM_Bridge
  imports "SubsetSum_DecisionTree"
begin

section ‹DTM bridge: abstract run model›

fun wf_run where
  "wf_run L R oL oR (Leaf b) = True"
| "wf_run L R oL oR (AskL i U1 U2) =
     (i ∈ L ∧ wf_run L R oL oR (if oL i then U2 else U1))"
| "wf_run L R oL oR (AskR j U1 U2) =
     (j ∈ R ∧ wf_run L R oL oR (if oR j then U2 else U1))"

fun tm_to_dtr' ::
  "('C ⇒ int) ⇒ ('C ⇒ bool ⇒ 'C) ⇒ ('C ⇒ bool) ⇒ nat ⇒ 'C ⇒ (nat,nat) dtr"
where
  "tm_to_dtr' head0 stepf final_acc 0 c = Leaf (final_acc c)"
| "tm_to_dtr' head0 stepf final_acc (Suc t) c =
     AskL (nat (head0 c))
          (tm_to_dtr' head0 stepf final_acc t (stepf c False))
          (tm_to_dtr' head0 stepf final_acc t (stepf c True))"

locale DTM_Run =
  fixes steps   :: "'M ⇒ bool list ⇒ nat"          (* halting time on input x *)
    and conf    :: "'M ⇒ bool list ⇒ nat ⇒ 'C"     (* configuration after t steps *)
    and head0   :: "'C ⇒ int"                      (* position of input-tape head *)
    and accepts :: "'M ⇒ bool list ⇒ bool"         (* acceptance predicate *)
begin

definition read0 :: "'M ⇒ bool list ⇒ nat set" where
  "read0 M x = (λt. nat (head0 (conf M x t))) ` {..< steps M x}"

lemma finite_read0[simp]: "finite (read0 M x)"
  unfolding read0_def by (intro finite_imageI) simp

lemma card_read0_le_steps:
  "card (read0 M x) ≤ steps M x"
  unfolding read0_def by (metis card_image_le card_lessThan finite_lessThan)

end

section ‹Contiguous overwrite (splice)›

definition splice :: "nat ⇒ nat ⇒ bool list ⇒ bool list ⇒ bool list" where
  "splice a w xs bs = take a xs @ bs @ drop (a + w) xs"

lemma splice_nth_inside:
  assumes LEN: "length bs = w"
      and BND: "a + w ≤ length xs"
      and IN1: "a ≤ i"
      and IN2: "i < a + w"
  shows "splice a w xs bs ! i = bs ! (i - a)"
proof -
  have ia_lt: "i - a < w" using IN1 IN2 by arith
  have a_le_len: "a ≤ length xs" using BND by linarith
  have "splice a w xs bs ! i = (take a xs @ bs @ drop (a + w) xs) ! i"
    by (simp add: splice_def)
  also have "... = (bs @ drop (a + w) xs) ! (i - a)"
    using IN1 a_le_len by (simp add: nth_append)
  also have "... = bs ! (i - a)"
    using ia_lt LEN by (simp add: nth_append)
  finally show ?thesis .
qed

lemma splice_nth_left:
  assumes BND: "a ≤ length xs"
      and L:   "i < a"
  shows "splice a w xs bs ! i = xs ! i"
  using assms by (simp add: splice_def nth_append)

lemma splice_nth_right:
  assumes LEN: "length bs = w"
      and BND: "a + w ≤ length xs"
      and R:   "a + w ≤ i"
  shows "splice a w xs bs ! i = xs ! i"
proof -
  have a_le_len: "a ≤ length xs" using BND by linarith
  have i_ge_a:   "a ≤ i"         using R   by linarith
  have i_minus_ge_w: "i - a ≥ w" using R   by arith
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

lemma splice_outside_left:
  assumes "i < a" "a ≤ length xs"
  shows   "splice a w xs ys ! i = xs ! i"
  using assms by (simp add: splice_nth_left)

lemma splice_outside_right:
  assumes "a + w ≤ i" "length ys = w" "a + w ≤ length xs"
  shows   "splice a w xs ys ! i = xs ! i"
  using assms by (simp add: splice_nth_right)

section ‹DTM semantics sufficient for unread-agreement›

locale DTM_Run_Sem =
  fixes steps     :: "'M ⇒ bool list ⇒ nat"
    and conf      :: "'M ⇒ bool list ⇒ nat ⇒ 'C"
    and head0     :: "'C ⇒ int"
    and accepts   :: "'M ⇒ bool list ⇒ bool"
    and M         :: 'M
    and stepf     :: "'C ⇒ bool ⇒ 'C"
    and final_acc :: "'C ⇒ bool"
  assumes step_sem:
    "⋀x t. conf M x (Suc t) = stepf (conf M x t) (x ! nat (head0 (conf M x t)))"
  assumes steps_stable_raw:
    "⋀x y. (⋀i. i ∈ ((λt. nat (head0 (conf M x t))) ` {..< steps M x}) ⟹ x ! i = y ! i)
           ⟹ steps M x = steps M y"
  assumes accepts_sem:
    "⋀x. accepts M x = final_acc (conf M x (steps M x))"
  assumes conf0_same: "⋀x y. conf M x 0 = conf M y 0"
begin

primrec drive :: "nat ⇒ 'C ⇒ (nat ⇒ bool) ⇒ 'C" where
  "drive 0 c inp = c"
| "drive (Suc t) c inp =
     (let i = nat (head0 c); b = inp i in drive t (stepf c b) inp)"

lemma drive_conf_gen:
  "drive t (conf M x u) (λi. x ! i) = conf M x (u + t)"
proof (induction t arbitrary: u)
  case 0 show ?case by simp
next
  case (Suc t)
  have "drive (Suc t) (conf M x u) (λi. x ! i)
        = drive t (stepf (conf M x u) (x ! nat (head0 (conf M x u)))) (λi. x ! i)"
    by simp
  also have "... = drive t (conf M x (Suc u)) (λi. x ! i)"
    by (simp add: step_sem)
  also have "... = conf M x (Suc u + t)"
    by (simp add: Suc.IH)
  finally show ?case by simp
qed

lemma drive_conf:
  "drive t (conf M x 0) (λi. x ! i) = conf M x t"
  by (simp add: drive_conf_gen)

(* Decision tree eval matches the driven TM evolution *)
lemma run_tm_to_dtr':
  "run oL oR (tm_to_dtr' head0 stepf final_acc t c)
   = final_acc (drive t c oL)"
  by (induction t arbitrary: c) (simp_all add: Let_def)

(* Specialize to x and steps M x *)
lemma tm_to_dtr_correct:
  "run (λi. x ! i) (λi. x ! i)
        (tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0))
   = final_acc (conf M x (steps M x))"
  by (simp add: run_tm_to_dtr' drive_conf)

corollary tm_to_dtr_accepts:
  "run (λi. x ! i) (λi. x ! i)
        (tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0))
   = accepts M x"
  by (simp add: tm_to_dtr_correct accepts_sem)

(* local read-set, if you need it later *)
definition read0S :: "bool list ⇒ nat set" where
  "read0S x = (λt. nat (head0 (conf M x t))) ` {..< steps M x}"

(* handy: one-step shift for images over {..<t} to {..<Suc t} *)
lemma image_shift_suc_subset:
  fixes F :: "nat ⇒ 'a"
  shows "(λu. F u) ` {..<t} ⊆ F ` {..<Suc t}"
  by auto

lemma seenL_tm_to_dtr_subset_read0_helper:
  "seenL_run oL oR (tm_to_dtr' head0 stepf final_acc t c)
     ⊆ (λu. nat (head0 (drive u c oL))) ` {..< t}"
proof (induction t arbitrary: c)
  case 0
  show ?case by simp
next
  case (Suc t)
  let ?i = "nat (head0 c)"

  have root_in:
    "?i ∈ (λu. nat (head0 (drive u c oL))) ` {..< Suc t}"
    by (rule image_eqI[where x=0]) simp_all

  have IH_sub:
    "seenL_run oL oR
       (tm_to_dtr' head0 stepf final_acc t (stepf c (oL ?i)))
     ⊆ (λu. nat (head0 (drive u (stepf c (oL ?i)) oL))) ` {..< t}"
    by (rule Suc.IH)

  have drive_suc:
    "(λu. nat (head0 (drive u (stepf c (oL ?i)) oL)))
     = (λu. nat (head0 (drive (Suc u) c oL)))"
    by (intro ext) simp

  have sub_into_parent:
    "(λu. nat (head0 (drive (Suc u) c oL))) ` {..< t}
     ⊆ (λu. nat (head0 (drive u c oL))) ` {..< Suc t}"
  proof
    fix y
    assume "y ∈ (λu. nat (head0 (drive (Suc u) c oL))) ` {..< t}"
    then obtain u where u_lt: "u < t"
      and y_def: "y = nat (head0 (drive (Suc u) c oL))" by auto
    have "y = (λv. nat (head0 (drive v c oL))) (Suc u)"
      by (simp add: y_def)
    moreover have "Suc u ∈ {..< Suc t}"
      using u_lt by simp
    ultimately show "y ∈ (λu. nat (head0 (drive u c oL))) ` {..< Suc t}"
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
  defines "T ≡ tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0)"
  shows "seenL_run (λi. x ! i) (λj. x ! j) T ⊆ Base.read0 M x"
proof -
  have A:
    "seenL_run (λi. x ! i) (λj. x ! j)
       (tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0))
     ⊆ (λu. nat (head0 (drive u (conf M x 0) (λi. x ! i)))) ` {..< steps M x}"
    by (rule seenL_tm_to_dtr_subset_read0_helper)
  also have "… = (λu. nat (head0 (conf M x u))) ` {..< steps M x}"
    by (simp add: drive_conf)
  also have "… = Base.read0 M x"
    unfolding Base.read0_def by simp
  finally show ?thesis by (simp add: T_def)
qed

(* 1) Helper proved by induction on t *)
lemma seenR_tm_to_dtr_subset_read0_helper:
  "seenR_run oL oR (tm_to_dtr' head0 stepf final_acc t c)
     ⊆ (λu. nat (head0 (drive u c oL))) ` {..< t}"
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
       ⊆ (λu. nat (head0 (drive u (stepf c (oL ?i)) oL))) ` {..< t}"
    by (rule Suc.IH)
  have drive_suc:
    "(λu. nat (head0 (drive u (stepf c (oL ?i)) oL)))
     = (λu. nat (head0 (drive (Suc u) c oL)))"
    by (intro ext) simp
  have shift:
    "(λu. nat (head0 (drive (Suc u) c oL))) ` {..< t}
       ⊆ (λu. nat (head0 (drive u c oL))) ` {..< Suc t}"
  proof
    fix y assume "y ∈ (λu. nat (head0 (drive (Suc u) c oL))) ` {..< t}"
    then obtain u where u:"u < t" and y:"y = nat (head0 (drive (Suc u) c oL))" by auto
    have "Suc u ∈ {..< Suc t}" using u by simp
    have mem: "Suc u ∈ {..< Suc t}" using u by simp
    have eq:  "y = (λv. nat (head0 (drive v c oL))) (Suc u)" by (simp add: y)
    have "(λv. nat (head0 (drive v c oL))) (Suc u)
        ∈ (λv. nat (head0 (drive v c oL))) ` {..< Suc t}"
      using mem by (rule imageI)
    thus "y ∈ (λv. nat (head0 (drive v c oL))) ` {..< Suc t}"
      by (simp add: eq)
  qed
  from split IH_sub drive_suc shift show ?case by auto
qed

(* 2) Use the helper to get the version w.r.t. Base.read0 *)
lemma seenR_tm_to_dtr_subset_read0:
  fixes x :: "bool list"
  defines "T ≡ tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0)"
  shows "seenR_run (λi. x ! i) (λj. x ! j) T ⊆ Base.read0 M x"
proof -
  have
    "seenR_run (λi. x ! i) (λj. x ! j)
       (tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0))
     ⊆ (λu. nat (head0 (drive u (conf M x 0) (λi. x ! i)))) ` {..< steps M x}"
    by (rule seenR_tm_to_dtr_subset_read0_helper)
  also have "… = (λu. nat (head0 (conf M x u))) ` {..< steps M x}"
    by (simp add: drive_conf)
  also have "… = Base.read0 M x"
    unfolding Base.read0_def by simp
  finally show ?thesis by (simp add: T_def)
qed

(* Bridge fact: our local read0S equals the inherited read0. *)
lemma read0_bridge: "read0S x = Base.read0 M x"
  by (simp add: read0S_def Base.read0_def)

lemma steps_stable:
  assumes AG: "⋀i. i ∈ Base.read0 M x ⟹ x ! i = y ! i"
  shows "steps M x = steps M y"
proof (rule steps_stable_raw)
  fix i
  assume iIn: "i ∈ (λt. nat (head0 (conf M x t))) ` {..< steps M x}"
  (* 1) Turn it into membership in the local read-set *)
  have iR0S: "i ∈ read0S x"
    using iIn by (simp add: read0S_def)
  (* 2) Bridge to the locale’s read-set *)
  have iBase: "i ∈ Base.read0 M x"
    using iR0S by (simp add: read0_bridge)
  (* 3) Apply the assumption *)
  show "x ! i = y ! i" by (rule AG[OF iBase])
qed

(* helper: if t < steps, the index read at time t is in read0S *)
lemma idx_in_read0S:
  assumes "t < steps M x"
  shows "nat (head0 (conf M x t)) ∈ read0S x"
  using assms
  unfolding read0S_def
  by (intro image_eqI[where x=t]) simp_all

lemma unread_agreement:
  assumes AG: "⋀i. i ∈ Base.read0 M x ⟹ x ! i = y ! i"
  shows "accepts M x ⟷ accepts M y"
proof -
  (* same halting time *)
  have steps_eq: "steps M x = steps M y"
    by (rule steps_stable[OF AG])

  (* convert agreement to the local read-set once *)
  have AGS: "⋀i. i ∈ read0S x ⟹ x ! i = y ! i"
  proof -
    fix i assume "i ∈ read0S x"
    hence "i ∈ Base.read0 M x" by (simp add: read0_bridge)
    thus "x ! i = y ! i" by (rule AG)
  qed

  (* configurations match up to the halting time *)
  have conf_eq: "⋀t. t ≤ steps M x ⟹ conf M x t = conf M y t"
  proof-
    fix t :: nat
    show "t ≤ steps M x ⟹ conf M x t = conf M y t"
    proof (induction t)
      case 0
      show ?case by (simp add: conf0_same) 
    next
      case (Suc t)
  (* from Suc t ≤ steps … get the strict bound we actually need *)
      have t_lt: "t < steps M x" using Suc.prems by simp

  (* apply IH at t ≤ steps … *)
      have IH: "conf M x t = conf M y t" by (rule Suc.IH) (use Suc.prems in simp)

      let ?i = "nat (head0 (conf M x t))"

  (* the scanned index at time t is in the read-set *)
      have i_mem: "?i ∈ read0S x"
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

abbreviation sp :: "nat ⇒ nat ⇒ bool list ⇒ bool list ⇒ bool list" where
  "sp ≡ SubsetSum_DTM_Bridge.splice"

end

section ‹Catalog blocks and padded encoding›

text ‹We serialize the sets of LHS/RHS values into non-overlapping bit-blocks.›

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

text ‹Fixed block width; later you can make it logarithmic in the values.›
definition W :: "int list ⇒ int ⇒ nat" where
  "W as s = max 1 (length as)"

definition offL :: "int list ⇒ int ⇒ nat ⇒ nat" where
  "offL as s j = j * W as s"

definition offR :: "int list ⇒ int ⇒ nat ⇒ nat ⇒ nat" where
  "offR as s k j = length (enumL as s k) * W as s + j * W as s"

definition blockL :: "int list ⇒ int ⇒ nat ⇒ nat set" where
  "blockL as s j = { offL as s j ..< offL as s j + W as s }"

definition blockR :: "int list ⇒ int ⇒ nat ⇒ nat ⇒ nat set" where
  "blockR as s k j = { offR as s k j ..< offR as s k j + W as s }"

definition blockL_abs ::
  "(int list ⇒ int ⇒ bool list) ⇒ int list ⇒ int ⇒ nat ⇒ nat set" where
  "blockL_abs E as s j =
     { length (E as s) + offL as s j ..<
       length (E as s) + offL as s j + W as s }"

definition blockR_abs ::
  "(int list ⇒ int ⇒ bool list) ⇒ int list ⇒ int ⇒ nat ⇒ nat ⇒ nat set" where
  "blockR_abs E as s k j =
     { length (E as s) + offR as s k j ..<
       length (E as s) + offR as s k j + W as s }"

lemma blockL_abs_disjoint:
  assumes "j ≠ j'"
  shows   "blockL_abs E as s j ∩ blockL_abs E as s j' = {}"
proof -
  let ?W = "W as s"
  let ?c = "length (E as s)"
  have "j < j' ∨ j' < j" using assms by arith
  then show ?thesis
  proof
    assume lt: "j < j'"
    have "(Suc j) * ?W ≤ j' * ?W"
      using lt by (intro mult_right_mono) simp_all
    hence "?c + j * ?W + ?W ≤ ?c + j' * ?W" by simp
    thus ?thesis by (auto simp: blockL_abs_def offL_def)
  next
    assume lt: "j' < j"
    have "(Suc j') * ?W ≤ j * ?W"
      using lt by (intro mult_right_mono) simp_all
    hence "?c + j' * ?W + ?W ≤ ?c + j * ?W" by simp
    thus ?thesis by (auto simp: blockL_abs_def offL_def)
  qed
qed

lemma blockR_abs_disjoint:
  assumes "j ≠ j'"
  shows   "blockR_abs E as s k j ∩ blockR_abs E as s k j' = {}"
proof -
  let ?W = "W as s"
  let ?c = "length (E as s)"
  have "j < j' ∨ j' < j" using assms by arith
  then show ?thesis
  proof
    assume lt: "j < j'"
    have "(Suc j) * ?W ≤ j' * ?W"
      using lt by (intro mult_right_mono) simp_all
    hence "?c + offR as s k j + ?W ≤ ?c + offR as s k j'"
      by (simp add: offR_def add_mult_distrib2)
    thus ?thesis by (auto simp: blockR_abs_def)
  next
    assume lt: "j' < j"
    have "(Suc j') * ?W ≤ j * ?W"
      using lt by (intro mult_right_mono) simp_all
    hence "?c + offR as s k j' + ?W ≤ ?c + offR as s k j"
      by (simp add: offR_def add_mult_distrib2)
    thus ?thesis by (auto simp: blockR_abs_def)
  qed
qed

lemma blockL_abs_blockR_abs_disjoint:
  assumes jL: "j < length (enumL as s k)"
  shows   "blockL_abs E as s j ∩ blockR_abs E as s k j' = {}"
proof -
  let ?W = "W as s"
  let ?c = "length (E as s)"
  have step:
    "?c + offL as s j + ?W ≤ ?c + offR as s k j'"
  proof -
    have "(Suc j) * ?W ≤ length (enumL as s k) * ?W"
      using jL by (intro mult_right_mono) simp_all
    hence "?c + (Suc j) * ?W ≤ ?c + length (enumL as s k) * ?W" by simp
    also have "… ≤ ?c + (length (enumL as s k) * ?W + j' * ?W)" by simp
    finally show ?thesis
      by (simp add: offL_def offR_def add_mult_distrib2)
  qed
  show ?thesis
    using step by (auto simp: blockL_abs_def blockR_abs_def)
qed

(* same width, consecutive half-open blocks are disjoint when indices differ *)
lemma blocks_disjoint_same_base:
  fixes W :: nat
  assumes "W > 0" and "j ≠ j'"
  shows "{j*W ..< j*W + W} ∩ {j'*W ..< j'*W + W} = {}"
proof -
  have "j < j' ∨ j' < j" using assms(2) by arith
  then show ?thesis
  proof
    assume lt: "j < j'"
    have "(Suc j) * W ≤ j' * W"
      using lt assms(1) by (intro mult_right_mono) simp_all
    hence "j*W + W ≤ j'*W" by simp
    thus ?thesis by auto
  next
    assume lt: "j' < j"
    have "(Suc j') * W ≤ j * W"
      using lt assms(1) by (intro mult_right_mono) simp_all
    hence "j'*W + W ≤ j*W" by simp
    thus ?thesis by auto
  qed
qed

(* Disjointness results *)
lemma blockL_disjoint:
  assumes "j ≠ j'"
  shows   "blockL as s j ∩ blockL as s j' = {}"
proof -
  have Wpos: "W as s > 0" by (simp add: W_def)
  have base:
    "{offL as s j ..< offL as s j + W as s}
     ∩ {offL as s j' ..< offL as s j' + W as s} = {}"
    using blocks_disjoint_same_base[of "W as s" j j'] Wpos assms
    by (simp add: offL_def)
  show ?thesis using blockL_def base by simp
qed

lemma blockR_disjoint:
  assumes "j ≠ j'"
  shows "blockR as s k j ∩ blockR as s k j' = {}"
proof -
  have "j < j' ∨ j' < j" using assms by arith
  then show ?thesis
  proof
    assume lt: "j < j'"
    have "(Suc j) * W as s ≤ j' * W as s"
      using lt by (intro mult_right_mono) simp_all
    hence "offR as s k j + W as s ≤ offR as s k j'"
      by (simp add: offR_def algebra_simps)   (* j*W + W = (Suc j)*W *)
    thus ?thesis by (auto simp: blockR_def)
  next
    assume lt: "j' < j"
    have "(Suc j') * W as s ≤ j * W as s"
      using lt by (intro mult_right_mono) simp_all
    hence "offR as s k j' + W as s ≤ offR as s k j"
      by (simp add: offR_def algebra_simps)
    thus ?thesis by (auto simp: blockR_def)
  qed
qed

lemma blockL_blockR_disjoint:
  assumes jL: "j < length (enumL as s k)"
  shows "blockL as s j ∩ blockR as s k j' = {}"
proof -
  let ?W = "W as s"
  let ?base = "length (enumL as s k) * ?W"

  have Suc_le: "Suc j ≤ length (enumL as s k)" using jL by simp
  have topL: "offL as s j + ?W ≤ ?base"
  proof -
    have "offL as s j + ?W = (j + 1) * ?W"
      by (simp add: offL_def add_mult_distrib2)
    also have "... ≤ length (enumL as s k) * ?W"
      using Suc_le by (intro mult_right_mono) simp_all
    finally show ?thesis .
  qed

  have "blockL as s j ⊆ {..< ?base}"
  proof
    fix x assume xL: "x ∈ blockL as s j"
    have x_lt: "x < offL as s j + W as s"
      using xL by (simp add: blockL_def)
    have "x < length (enumL as s k) * W as s"
      using x_lt topL by (rule less_le_trans)
    thus "x ∈ {..< length (enumL as s k) * W as s}"
  by simp
  qed
  moreover
  have "blockR as s k j' ⊆ {?base ..< ?base + ?W + j' * ?W}"
    by (auto simp: blockR_def offR_def W_def)
  ultimately show ?thesis by fastforce
qed

section ‹Padding encoder›

locale SubsetSum_Padded_Enc =
  fixes enc0      :: "int list ⇒ int ⇒ bool list"     (* baseline CL encoding *)
    and to_bits   :: "nat ⇒ int ⇒ bool list"           (* fixed-width bits of an integer *)
    and from_bits :: "bool list ⇒ int"
  assumes bits_roundtrip:
    "⋀as s k v. v ∈ set (enumL as s k) ∪ set (enumR as s k) ⟹
       length (to_bits (W as s) v) = W as s ∧ from_bits (to_bits (W as s) v) = v"
begin

definition padL where
  "padL as s k = concat (map (to_bits (W as s)) (enumL as s k))"

definition padR where
  "padR as s k = concat (map (to_bits (W as s)) (enumR as s k))"

definition enc where
  "enc as s k = enc0 as s @ padL as s k @ padR as s k"

(* Sum of a constant over any list *)
lemma sum_const_all_nat: "(∑ _← L. (c::nat)) = length L * c" for L c
  by (induction L) simp_all

(* helper: length rule on elements of enumL / enumR *)
lemma to_bits_len_on_enumL:
  assumes vL: "v ∈ set (enumL as s k)"
  shows   "length (to_bits (W as s) v) = W as s"
proof -
  have inU: "v ∈ set (enumL as s k) ∪ set (enumR as s k)"
    using vL by auto   (* or: by (rule UnI1) *)
  from bits_roundtrip[OF inU] show ?thesis by simp
qed

lemma to_bits_len_on_enumR:
  assumes vR: "v ∈ set (enumR as s k)"
  shows   "length (to_bits (W as s) v) = W as s"
proof -
  have inU: "v ∈ set (enumL as s k) ∪ set (enumR as s k)"
    using vR by auto   (* or: by (rule UnI2) *)
  from bits_roundtrip[OF inU] show ?thesis by simp
qed

(* pointwise constant-length maps over the enumerations *)
lemma map_len_to_bits_constL:
  "map (λv. length (to_bits (W as s) v)) (enumL as s k)
   = map (λ_. W as s) (enumL as s k)"
  by (rule map_cong[OF refl]) (simp add: to_bits_len_on_enumL)

lemma map_len_to_bits_constR:
  "map (λv. length (to_bits (W as s) v)) (enumR as s k)
   = map (λ_. W as s) (enumR as s k)"
  by (rule map_cong[OF refl]) (simp add: to_bits_len_on_enumR)

lemma length_padL:
  "length (padL as s k) = length (enumL as s k) * W as s"
proof -
  have "length (padL as s k)
        = sum_list (map (length ∘ to_bits (W as s)) (enumL as s k))"
    by (simp add: padL_def length_concat)
  also have "... = sum_list (map (λv. length (to_bits (W as s) v)) (enumL as s k))"
    by (simp add: comp_def)
  also have "... = sum_list (map (λ_. W as s) (enumL as s k))"
    by (simp add: map_len_to_bits_constL)
  also have "... = length (enumL as s k) * W as s"
    by (rule sum_const_all_nat)
  finally show ?thesis .
qed

lemma length_padR:
  "length (padR as s k) = length (enumR as s k) * W as s"
proof -
  have "length (padR as s k)
        = sum_list (map (length ∘ to_bits (W as s)) (enumR as s k))"
    by (simp add: padR_def length_concat)
  also have "... = sum_list (map (λv. length (to_bits (W as s) v)) (enumR as s k))"
    by (simp add: comp_def)
  also have "... = sum_list (map (λ_. W as s) (enumR as s k))"
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

section ‹Coverage via unread-agreement›

locale Coverage_TM =
  DTM_Run_Sem steps conf head0 accepts M stepf final_acc +
  SubsetSum_Padded_Enc enc0 to_bits from_bits
  for steps :: "'M ⇒ bool list ⇒ nat"
  and conf  :: "'M ⇒ bool list ⇒ nat ⇒ 'C"
  and head0 :: "'C ⇒ int"
  and accepts :: "'M ⇒ bool list ⇒ bool"
  and M :: 'M
  and stepf :: "'C ⇒ bool ⇒ 'C"
  and final_acc :: "'C ⇒ bool"
  and enc0  :: "int list ⇒ int ⇒ bool list"
  and to_bits :: "nat ⇒ int ⇒ bool list"
  and from_bits :: "bool list ⇒ int"
  +
fixes kk :: nat

  assumes correctness:
    "accepts M (enc as s kk)
       ⟷ good as s (λi. (enc as s kk) ! i) (λj. (enc as s kk) ! j)"
  assumes read0_after_enc0:
    "Base.read0 M (enc as s kk)
       ⊆ { length (enc0 as s)
          ..< length (enc0 as s) + length (padL as s kk) + length (padR as s kk) }"
begin

abbreviation x0 :: "int list ⇒ int ⇒ bool list" where
  "x0 as s ≡ enc as s kk"

definition touches :: "bool list ⇒ nat set ⇒ bool" where
  "touches x B ⟷ Base.read0 M x ∩ B ≠ {}"

lemma offL_window_in_enc:
  assumes jL: "j < length (enumL as s kk)"
  shows "length (enc0 as s) + offL as s j + W as s ≤ length (enc as s kk)"
proof -
  have pad_bound:
    "offL as s j + W as s ≤ length (padL as s kk) + length (padR as s kk)"
  proof -
    have "(Suc j) * W as s
            ≤ (length (enumL as s kk) + length (enumR as s kk)) * W as s"
      using jL by (intro mult_right_mono) simp_all
    then show ?thesis
      by (simp add: offL_def length_padL length_padR add_mult_distrib2 algebra_simps)
  qed

  have "length (enc0 as s) + offL as s j + W as s
        = length (enc0 as s) + (offL as s j + W as s)" by simp
  also have "… ≤ length (enc0 as s) + (length (padL as s kk) + length (padR as s kk))"
    using pad_bound by (rule add_left_mono)
  also have "… = length (enc as s kk)"
    by (simp add: enc_def)
  finally show ?thesis .
qed

lemma offR_window_in_enc:
  assumes jR: "j < length (enumR as s kk)"
  shows "length (enc0 as s) + offR as s kk j + W as s ≤ length (enc as s kk)"
proof -
  have "(Suc j) * W as s ≤ length (enumR as s kk) * W as s"
    using jR by (intro mult_right_mono) simp_all
  hence offR_le:
    "offR as s kk j + W as s ≤ length (padL as s kk) + length (padR as s kk)"
    by (simp add: offR_def length_padL length_padR add_mult_distrib2 algebra_simps)
  then show ?thesis
    by (simp add: enc_def add_left_mono)
qed

definition Lval_at :: "int list ⇒ int ⇒ (nat ⇒ bool) ⇒ nat ⇒ int" where
  "Lval_at as s oL j =
     from_bits (map oL [length (enc0 as s) + offL as s j  ..<  length (enc0 as s) + offL as s j + W as s])"

definition Rval_at :: "int list ⇒ int ⇒ (nat ⇒ bool) ⇒ nat ⇒ int" where
  "Rval_at as s oR j =
     from_bits (map oR [length (enc0 as s) + offR as s kk j ..<  length (enc0 as s) + offR as s kk j + W as s])"

(* 1) The index sets we want fully covered *)
definition Lset where
  "Lset as s ≡ ⋃ j < length (enumL as s kk). blockL_abs enc0 as s j"

definition Rset where
  "Rset as s ≡ ⋃ j < length (enumR as s kk). blockR_abs enc0 as s kk j"

(* 2) The decision tree extracted from the TM on input x = enc as s kk *)
definition T where
  "T as s ≡
     tm_to_dtr' head0 stepf final_acc
       (steps M (enc as s kk))
       (conf M (enc as s kk) 0)"

(* 3) The semantic predicate that the DT computes (pure spec; no bitstrings) *)
definition good where
  "good as s oL oR ≡
     (∃jL<length (enumL as s kk). ∃jR<length (enumR as s kk).
        Lval_at as s oL jL = Rval_at as s oR jR)"

lemma in_padL_imp_in_some_blockL_abs:
  assumes i_in:
    "i ∈ {length (enc0 as s) ..< length (enc0 as s) + length (padL as s kk)}"
  shows "∃j<length (enumL as s kk). i ∈ blockL_abs enc0 as s j"
proof -
  let ?len0 = "length (enc0 as s)"
  let ?W    = "W as s"
  let ?E    = "enumL as s kk"
  let ?k    = "i - ?len0"

  have i_ge: "?len0 ≤ i" and i_lt: "i < ?len0 + length (padL as s kk)"
    using i_in by auto
  hence k_lt: "?k < length (padL as s kk)" by simp

  (* From membership, the padL interval is non-empty → W > 0 *)
  have Wpos: "0 < ?W"
  proof (rule ccontr)
    assume "¬ 0 < ?W" hence "?W = 0" by simp
    hence "length (padL as s kk) = 0" by (simp add: length_padL)
    have "length (padL as s kk) = 0" by (simp add: ‹length (padL as s kk) = 0›)
    then have "i ∈ {length (enc0 as s) ..< length (enc0 as s) + 0}" using i_in by simp
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
  ultimately have "i ∈ blockL_abs enc0 as s j"
    using r_lt by auto

  thus ?thesis by (intro exI[of _ j]) (use j_lt in simp)
qed

lemma in_padR_imp_in_some_blockR_abs:
  assumes iR:
    "i ∈ { length (enc0 as s) + length (padL as s kk)
         ..< length (enc0 as s) + length (padL as s kk) + length (padR as s kk) }"
  shows "∃j<length (enumR as s kk). i ∈ blockR_abs enc0 as s kk j"
proof -
  let ?base = "length (enc0 as s) + length (padL as s kk)"
  let ?W    = "W as s"
  let ?r    = "i - ?base"

  from iR have base_le: "?base ≤ i"
    and r_lt: "?r < length (padR as s kk)"
    by auto

  have padR_len: "length (padR as s kk) = length (enumR as s kk) * ?W"
    by (simp add: length_padR)

  (* show W>0; otherwise padR would be empty, contradicting r_lt *)
  have Wpos: "0 < ?W"
  proof (rule ccontr)
    assume "¬ 0 < ?W"
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
  have base_le: "?base ≤ i" and r_lt: "i - ?base < length (padR as s kk)"
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

have u_ge0: "0 ≤ u" by simp   (* nat is nonnegative *)

have mem:
  "length (enc0 as s) + length (padL as s kk) + j * W as s ≤ i ∧
   i < length (enc0 as s) + length (padL as s kk) + j * W as s + W as s"
  using i_decomp j_def u_def u_lt by force

have "i ∈ blockR_abs enc0 as s kk j"
  using mem
  by (simp add: BR_eq)

  thus ?thesis using j_lt by blast
qed

lemma read0_subset_blocks_abs:
  "Base.read0 M (enc as s kk) ⊆ Lset as s ∪ Rset as s"
proof
  fix i assume iR: "i ∈ Base.read0 M (enc as s kk)"

  have len_enc:
    "length (enc as s kk)
     = length (enc0 as s) + length (padL as s kk) + length (padR as s kk)"
    by (simp add: enc_def)

  (* 1) First, land i in the big half-open interval after enc0 *)
  from read0_after_enc0 iR have i_band:
    "i ∈ { length (enc0 as s)
         ..< length (enc0 as s) + length (padL as s kk) + length (padR as s kk) }"
    by (rule subsetD)

  (* 2) Split i_band into the two inequalities we will feed to the L/R lemmas *)
  have base_le:   "length (enc0 as s) ≤ i"
    and  i_lt_enc: "i < length (enc0 as s) + length (padL as s kk) + length (padR as s kk)"
    using i_band by auto

  (* 3) Case split: i lies either in padL or in padR *)
  have disj:
    "i < length (enc0 as s) + length (padL as s kk) ∨
     length (enc0 as s) + length (padL as s kk) ≤ i" by linarith

  from disj show "i ∈ Lset as s ∪ Rset as s"
  proof
    (* ---- L-branch ---- *)
    assume i_lt_L: "i < length (enc0 as s) + length (padL as s kk)"
    have i_in_padL_set:
      "i ∈ { length (enc0 as s) ..< length (enc0 as s) + length (padL as s kk) }"
      using base_le i_lt_L by simp
    from in_padL_imp_in_some_blockL_abs[OF i_in_padL_set]
    obtain j where jL: "j < length (enumL as s kk)"
               and iBL: "i ∈ blockL_abs enc0 as s j" by blast
    have "i ∈ Lset as s"
      unfolding Lset_def by (intro UN_I[of j]) (use jL iBL in auto)
    thus ?thesis by simp

  next
    (* ---- R-branch ---- *)
    assume ge: "length (enc0 as s) + length (padL as s kk) ≤ i"
    have i_in_padR_set:
      "i ∈ { length (enc0 as s) + length (padL as s kk)
           ..< length (enc0 as s) + length (padL as s kk) + length (padR as s kk) }"
      using ge i_lt_enc by simp
    from in_padR_imp_in_some_blockR_abs[OF i_in_padR_set]
    obtain j where jR: "j < length (enumR as s kk)"
               and iBR: "i ∈ blockR_abs enc0 as s kk j" by blast
    have "i ∈ Rset as s"
      unfolding Rset_def by (intro UN_I[of j]) (use jR iBR in auto)
    thus ?thesis by simp
  qed
qed

lemma wf_run_of_seen:
  assumes "seenL_run oL oR U ⊆ L" and "seenR_run oL oR U ⊆ R"
  shows   "wf_run L R oL oR U"
  using assms by (induction U) auto

lemma wf_of_seen_run:
  assumes "seenL_run oL oR U ⊆ L" "seenR_run oL oR U ⊆ R"
  shows   "wf_run L R oL oR U"
  using assms by (induction U) (auto split: if_splits)

lemma wf_T_union_run:
  "wf_run (Lset as s ∪ Rset as s) (Lset as s ∪ Rset as s)
          ((!) (enc as s kk)) ((!) (enc as s kk))
          (tm_to_dtr' head0 stepf final_acc (steps M (enc as s kk))
                       (conf M (enc as s kk) 0))"
proof -
  let ?x = "enc as s kk"
  let ?T = "tm_to_dtr' head0 stepf final_acc (steps M ?x) (conf M ?x 0)"

  (* your SL0 / SR0 / subset derivations exactly as you already have: *)
  have SL1:
    "seenL_run ((!) ?x) ((!) ?x) ?T
       ⊆ (λu. nat (head0 (drive u (conf M ?x 0) ((!) ?x)))) ` {..< steps M ?x}"
    by (rule seenL_tm_to_dtr_subset_read0_helper)
  have SL0: "seenL_run ((!) ?x) ((!) ?x) ?T ⊆ Base.read0 M ?x"
    using SL1 by (simp add: drive_conf Base.read0_def)

  have SR1:
    "seenR_run ((!) ?x) ((!) ?x) ?T
       ⊆ (λu. nat (head0 (drive u (conf M ?x 0) ((!) ?x)))) ` {..< steps M ?x}"
    by (rule seenR_tm_to_dtr_subset_read0_helper)
  have SR0: "seenR_run ((!) ?x) ((!) ?x) ?T ⊆ Base.read0 M ?x"
    using SR1 by (simp add: drive_conf Base.read0_def)

  have R0_sub: "Base.read0 M ?x ⊆ Lset as s ∪ Rset as s"
    by (rule read0_subset_blocks_abs)

  have SL: "seenL_run ((!) ?x) ((!) ?x) ?T ⊆ Lset as s ∪ Rset as s"
    using SL0 R0_sub by auto
  have SR: "seenR_run ((!) ?x) ((!) ?x) ?T ⊆ Lset as s ∪ Rset as s"
    using SR0 R0_sub by auto

  show ?thesis by (rule wf_of_seen_run[OF SL SR])
qed

(* 5) Correctness of the tree wrt the spec *)
lemma correct_T:
  "run (λi. (enc as s kk) ! i) (λj. (enc as s kk) ! j) (T as s)
   = good as s (λi. (enc as s kk) ! i) (λj. (enc as s kk) ! j)"
proof -
  have "run (λi. (enc as s kk) ! i) (λj. (enc as s kk) ! j) (T as s)
        = run ((!) (enc as s kk)) ((!) (enc as s kk))
             (tm_to_dtr' head0 stepf final_acc (steps M (enc as s kk))
                (conf M (enc as s kk) 0))"
    by (simp add: T_def)
  also have "… = accepts M (enc as s kk)"
    by (simp add: tm_to_dtr_accepts)   (* from DTM_Run_Sem context *)
  also have "… = good as s (λi. (enc as s kk) ! i) (λj. (enc as s kk) ! j)"
    by (simp add: correctness)
  finally show ?thesis .
qed

lemma nth_concat_map_fixed:
  fixes xs :: "'a list" and f :: "'a ⇒ 'b list" and w :: nat
  assumes LEN: "⋀x. x ∈ set xs ⟹ length (f x) = w"
    and j: "j < length xs"
    and t: "t < w"
  shows "concat (map f xs) ! (j*w + t) = f (xs!j) ! t"
proof -
  (* 1) length of the concatenation over the first j chunks is j*w *)
  have pref_len: "length (concat (map f (take j xs))) = j * w"
  proof -
    have "length (concat (map f (take j xs)))
        = sum_list (map (length ∘ f) (take j xs))"
      by (simp add: length_concat)
    also have "... = (∑_← take j xs. w)"
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
  shows "Rval_at as s (λi. (enc as s kk) ! i) j = enumR as s kk ! j"
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
      "⋀x. x ∈ set (enumR as s kk) ⟹ length (to_bits (W as s) x) = ?w"
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

  have v_inR: "enumR as s kk ! j ∈ set (enumR as s kk)"
    using jR in_set_conv_nth by metis

  have v_inU:
    "enumR as s kk ! j ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
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
  "set (map (Rval_at as s (λi. (enc as s kk) ! i))
             [0..<length (enumR as s kk)])
   = set (enumR as s kk)"
proof -
  let ?n = "length (enumR as s kk)"
  have map_eq:
    "map (Rval_at as s ((!) (x0 as s))) [0..<?n]
     = map (λj. enumR as s kk ! j) [0..<?n]"
    by (rule map_cong[OF _])
       (simp_all add: Rval_at_on_enc_block)

  have set_map_nth:
    "set (map (λj. enumR as s kk ! j) [0..<?n]) = set (enumR as s kk)"
    using set_conv_nth by (simp add: map_nth)

  show ?thesis
    using map_eq set_map_nth by force
qed

lemma flipL_pointwise_enc:
  fixes j :: nat
  assumes jL:  "j < length (enumL as s kk)"
      and L2:  "2 ≤ length (enumL as s kk)"
      and hit:  "∃v∈set (enumL as s kk). v ∈ set (enumR as s kk)"
      and miss: "∃v∈set (enumL as s kk). v ∉ set (enumR as s kk)"
      and baseline_only_j:
        "good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟶
         (∀j'<length (enumL as s kk). j' ≠ j ⟶
            Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk))"
  shows "∃oL'. (∀i. i ∉ blockL_abs enc0 as s j ⟶ oL' i = (x0 as s) ! i)
              ∧ good as s oL' ((!) (x0 as s))
                ≠ good as s ((!) (x0 as s)) ((!) (x0 as s))"
proof -
  obtain v_in where v_inL: "v_in ∈ set (enumL as s kk)" and v_inR: "v_in ∈ set (enumR as s kk)"
    using hit by blast
  obtain v_out where v_outL: "v_out ∈ set (enumL as s kk)" and v_outNR: "v_out ∉ set (enumR as s kk)"
    using miss by blast

  let ?a = "length (enc0 as s) + offL as s j"
  let ?w = "W as s"

  obtain bv_in  where bv_in_len:  "length bv_in  = ?w" and bv_in_val:  "from_bits bv_in  = v_in"
    using v_inL bits_roundtrip by blast
  obtain bv_out where bv_out_len: "length bv_out = ?w" and bv_out_val: "from_bits bv_out = v_out"
    using v_outL bits_roundtrip by blast

  define oL_in  where "oL_in  i = (if i ∈ blockL_abs enc0 as s j then bv_in  ! (i - ?a) else (x0 as s) ! i)" for i
  define oL_out where "oL_out i = (if i ∈ blockL_abs enc0 as s j then bv_out ! (i - ?a) else (x0 as s) ! i)" for i

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
      have inblk: "?a + t ∈ blockL_abs enc0 as s j" using tw by (simp add: blk_eq)
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
      have inblk: "?a + t ∈ blockL_abs enc0 as s j" using tw by (simp add: blk_eq)
      show "map oL_out [?a ..< ?a + ?w] ! t = bv_out ! t"
        using nth_map idx oL_out_def inblk by (simp add: tw)
    qed
    show ?thesis by (simp add: Lval_at_def slice bv_out_val)
  qed

  (* unchanged slices for j' ≠ j *)
  have same_block:
    "⋀j'. j' ≠ j ⟹ Lval_at as s oL_out j' = Lval_at as s ((!) (x0 as s)) j'"
  proof -
    fix j' assume ne: "j' ≠ j"
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
      have in_j': "?a' + t ∈ blockL_abs enc0 as s j'" using tw by (simp add: blk')
      have not_in_j: "?a' + t ∉ blockL_abs enc0 as s j"
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
     ⟷ (∃jL<length (enumL as s kk). Lval_at as s oL jL ∈ set (enumR as s kk))"
    for oL
  proof
    assume "good as s oL ((!) (x0 as s))"
    then obtain jL jR where jL: "jL < length (enumL as s kk)" and jR: "jR < length (enumR as s kk)"
      and eq: "Lval_at as s oL jL = Rval_at as s ((!) (x0 as s)) jR"
      by (auto simp: good_def)
    hence "Lval_at as s oL jL ∈ set (enumR as s kk)"
      using R_catalog jR by (auto simp: in_set_conv_nth)
    thus "∃jL<length (enumL as s kk). Lval_at as s oL jL ∈ set (enumR as s kk)" using jL by blast
  next
    assume "∃jL<length (enumL as s kk). Lval_at as s oL jL ∈ set (enumR as s kk)"
    then obtain jL where jL: "jL < length (enumL as s kk)"
      and mem: "Lval_at as s oL jL ∈ set (enumR as s kk)" by blast
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
      "⋀j'. j' < length (enumL as s kk) ⟹ j' ≠ j ⟹
         Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk)"
      using baseline_only_j True by blast

    have not_good_out: "¬ good as s oL_out ((!) (x0 as s))"
    proof
      assume H: "good as s oL_out ((!) (x0 as s))"
      then obtain j' where j'lt: "j' < length (enumL as s kk)"
        and mem': "Lval_at as s oL_out j' ∈ set (enumR as s kk)"
        by (auto simp: Good_char)
      show False
      proof (cases "j' = j")
        case True
        with Lval_out v_outNR show False
        using mem' by blast
      next
        case False
        have "Lval_at as s ((!) (x0 as s)) j' ∈ set (enumR as s kk)"
          using same_block[OF False] mem' by simp
        with no_other[OF j'lt False] show False by contradiction
      qed
    qed

    have outside_out: "∀i. i ∉ blockL_abs enc0 as s j ⟶ oL_out i = (x0 as s) ! i"
      by (simp add: oL_out_def)

    show ?thesis
      by (intro exI[of _ oL_out]) (use outside_out True not_good_out in auto)

  next
    case False
    (* create a witness at j *)
    have good_in': "good as s oL_in ((!) (x0 as s))"
      using Good_char jL Lval_in v_inR by blast

    have outside_in: "∀i. i ∉ blockL_abs enc0 as s j ⟶ oL_in i = (x0 as s) ! i"
      by (simp add: oL_in_def)

    show ?thesis
      by (intro exI[of _ oL_in]) (use outside_in False good_in' in auto)
  qed
qed

lemma run_agrees_on_seen:
  fixes T :: "('i,'j) dtr"
  assumes L: "⋀i. i ∈ seenL_run oL oR T ⟹ oL i = oL' i"
      and R: "⋀j. j ∈ seenR_run oL oR T ⟹ oR j = oR' j"
  shows "run oL oR T = run oL' oR' T"
  using L R by (induction T) auto

lemma flipR_pointwise_block:
  fixes oL oR :: "nat ⇒ bool" and j :: nat
  assumes jR: "j < length (enumR as s kk)"
      and R2: "2 ≤ length (enumR as s kk)"
  shows "∃oR'.
           (∀i. i ∉ blockR_abs enc0 as s kk j ⟶ oR' i = oR i)
         ∧ Rval_at as s oR' j ≠ Rval_at as s oR j"
proof -
  (* pick two different catalog values from enumR *)
  have len1: "1 < length (enumR as s kk)" using R2 by simp

  define u where "u = enumR as s kk ! 0"
  define v where "v = enumR as s kk ! 1"

  have u_in: "u ∈ set (enumR as s kk)"
    unfolding u_def nth_mem R2 by (meson len1 nth_mem order.strict_trans zero_less_one)
  have v_in: "v ∈ set (enumR as s kk)"
    unfolding v_def by (meson len1 nth_mem order.strict_trans zero_less_one)

  have distinct_enumR: "distinct (enumR as s kk)"
    by (simp add: enumR_def)  (* sorted_list_of_set -> distinct *)
  have uv_ne: "u ≠ v"
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
    "oR' i = (if ?a ≤ i ∧ i < ?a + ?w then bv ! (i - ?a) else oR i)" for i

  have outside_eq: "⋀i. i ∉ blockR_abs enc0 as s kk j ⟹ oR' i = oR i"
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
    have inblk: "?a ≤ ?a + i ∧ ?a + i < ?a + ?w"
      using iw by simp
    show "map oR' [?a ..< ?a + ?w] ! i = bv ! i"
      using nth_map idx oR'_def inblk by simp
  qed

  have new_val: "Rval_at as s oR' j = v"
    by (simp add: Rval_at_def slice_bv bv_val)

  (* either we already differ from v, or we first overwrite to u, which differs from v *)
  consider (diff) "Rval_at as s oR j ≠ v" | (eqv) "Rval_at as s oR j = v" by blast
  then show ?thesis
  proof cases
    case diff
    with outside_eq new_val show ?thesis by metis
  next
    case eqv
    (* overwrite to u to force a difference *)
    define oR_u where
      "oR_u i = (if ?a ≤ i ∧ i < ?a + ?w then bu ! (i - ?a) else oR i)" for i
    have slice_bu: "map oR_u [?a ..< ?a + ?w] = bu"
    proof (rule nth_equalityI)
      show "length (map oR_u [?a ..< ?a + ?w]) = length bu"
        by (simp add: bu_len)
    next
      fix i assume i_len: "i < length (map oR_u [?a ..< ?a + ?w])"
      hence iw: "i < ?w" by simp
      have idx: "[?a ..< ?a + ?w] ! i = ?a + i"
        using iw by simp
      have inblk: "?a ≤ ?a + i ∧ ?a + i < ?a + ?w"
        using iw by simp
      show "map oR_u [?a ..< ?a + ?w] ! i = bu ! i"
        using nth_map idx oR_u_def inblk by simp
    qed
    have old_to_u: "Rval_at as s oR_u j = u"
      by (simp add: Rval_at_def slice_bu bu_val)
    have diff_now: "Rval_at as s oR_u j ≠ Rval_at as s oR j"
      using eqv old_to_u uv_ne by simp
    have outside_eq_u: "∀i. i ∉ blockR_abs enc0 as s kk j ⟶ oR_u i = oR i"
      by (simp add: oR_u_def blockR_abs_def)
    from outside_eq_u diff_now show ?thesis by blast
  qed
qed

definition L0 where "L0 as s = Lset as s ∪ Rset as s"
definition R0 where "R0 as s = Lset as s ∪ Rset as s"
definition T0 where
  "T0 as s =
     tm_to_dtr' head0 stepf final_acc
       (steps M (enc as s kk))
       (conf  M (enc as s kk) 0)"
definition Good where "Good as s = good as s"

lemma seenL_T0_subset_read0:
  fixes x :: "bool list"
  assumes X: "x = enc as s kk"
  shows "seenL_run ((!) x) ((!) y) (T0 as s) ⊆ Base.read0 M x"
proof -
  let ?T = "tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0)"
  have T0_eq: "T0 as s = ?T" by (simp add: T0_def X)
  have "seenL_run ((!) x) ((!) y) ?T
          ⊆ (λu. nat (head0 (drive u (conf M x 0) ((!) x)))) ` {..< steps M x}"
    by (rule seenL_tm_to_dtr_subset_read0_helper)
  also have "... = (λu. nat (head0 (conf M x u))) ` {..< steps M x}"
    by (simp add: drive_conf)
  also have "... = Base.read0 M x"
    by (simp add: Base.read0_def)
  finally show ?thesis by (simp add: T0_eq)
qed

lemma seenR_T0_subset_read0:
  fixes x :: "bool list"
  assumes X: "x = enc as s kk"
  shows "seenR_run ((!) x) ((!) y) (T0 as s) ⊆ Base.read0 M x"
proof -
  let ?T = "tm_to_dtr' head0 stepf final_acc (steps M x) (conf M x 0)"
  have T0_eq: "T0 as s = ?T" by (simp add: T0_def X)
  have "seenR_run ((!) x) ((!) y) ?T
          ⊆ (λu. nat (head0 (drive u (conf M x 0) ((!) x)))) ` {..< steps M x}"
    by (rule seenR_tm_to_dtr_subset_read0_helper)
  also have "... = (λu. nat (head0 (conf M x u))) ` {..< steps M x}"
    by (simp add: drive_conf)
  also have "... = Base.read0 M x"
    by (simp add: Base.read0_def)
  finally show ?thesis by (simp add: T0_eq)
qed

(* NEW: run-wise well-formedness for the concrete input *)
lemma wf_T0_run:
  "wf_run (L0 as s) (R0 as s)
          ((!) (enc as s kk)) ((!) (enc as s kk))
          (T0 as s)"
  unfolding L0_def R0_def T0_def
  by (rule wf_T_union_run)

lemma correct_T0:
  "run ((!) (enc as s kk)) ((!) (enc as s kk)) (T0 as s)
   = Good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
proof -
  have "run ((!) (enc as s kk)) ((!) (enc as s kk)) (T0 as s)
        = run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
    by (simp add: T0_def T_def)
  also have "... = good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
    by (rule correct_T)
  finally show ?thesis
    by (simp add: Good_def)
qed

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
    have v_inL: "enumL as s kk ! j ∈ set (enumL as s kk)"
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
        have mono: "(Suc j) * ?w ≤ length (enumL as s kk) * ?w"
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
      "⋀v. v ∈ set (enumL as s kk) ⟹ length (to_bits (W as s) v) = ?w"
        by (simp add: to_bits_len_on_enumL)
    have fixed_len_meta:
      "⋀x'. x' ∈ set (enumL as s kk) ⟹ length (to_bits (W as s) x') = W as s"
      by (simp add: to_bits_len_on_enumL)
    thus "map ((!) (x0 as s)) [?a ..< ?a + ?w] ! t
          = to_bits (W as s) (enumL as s kk ! j) ! t"
      using nth_map idx
      by (smt (verit) ‹t < length (map ((!) (x0 as s)) 
        [length (enc0 as s) + offL as s j..< 
        length (enc0 as s) + offL as s j + W as s])› jL 
        length_map nth_concat_map_fixed step_enc_pad tw)
  qed
  have v_in: "enumL as s kk ! j ∈ set (enumL as s kk)"
    using jL in_set_conv_nth by metis
  have round: "from_bits (to_bits (W as s) (enumL as s kk ! j)) = enumL as s kk ! j"
    using SubsetSum_Padded_Enc.bits_roundtrip SubsetSum_Padded_Enc_axioms v_in 
    by blast
  show ?thesis
    by (simp add: Lval_at_def slice round)
qed

lemma Good_char_encR:
  "Good as s oL ((!) (x0 as s))
   ⟷ (∃jL<length (enumL as s kk). Lval_at as s oL jL ∈ set (enumR as s kk))"
proof
  (* ⇒ *)
  assume H: "Good as s oL ((!) (x0 as s))"
  then obtain jL jR where
    jL: "jL < length (enumL as s kk)" and jR: "jR < length (enumR as s kk)" and
    eq: "Lval_at as s oL jL = Rval_at as s ((!) (x0 as s)) jR"
    unfolding Good_def good_def by blast
  hence "Lval_at as s oL jL = enumR as s kk ! jR"
    by (simp add: Rval_at_on_enc_block jR)
  thus "∃jL<length (enumL as s kk). Lval_at as s oL jL ∈ set (enumR as s kk)"
    using jL in_set_conv_nth by (metis jR)
next
  (* ⇐ *)
  assume "∃jL<length (enumL as s kk). Lval_at as s oL jL ∈ set (enumR as s kk)"
  then obtain jL where jL: "jL < length (enumL as s kk)"
    and mem: "Lval_at as s oL jL ∈ set (enumR as s kk)" by blast
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
      and L2: "2 ≤ length (enumL as s kk)"
      and hit:  "∃v∈set (enumL as s kk). v ∈ set (enumR as s kk)"
      and miss: "∃v∈set (enumL as s kk). v ∉ set (enumR as s kk)"
      and baseline_only_j:
        "Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟶
        (∀j'<length (enumL as s kk). j' ≠ j ⟶
        Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk))"
  shows "∃oL'.
           (∀i. i ∉ blockL_abs enc0 as s j ⟶ oL' i = ((!) (enc as s kk)) i)
         ∧ Good as s oL' ((!) (enc as s kk))
           ≠ Good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
proof -
  let ?a = "length (enc0 as s) + offL as s j"
  let ?w = "W as s"
  (* pick two distinct L-catalog values to write *)
  have lt0: "0 < length (enumL as s kk)" and lt1: "1 < length (enumL as s kk)"
    using L2 by auto
  define p where "p = enumL as s kk ! 0"
  define q where "q = enumL as s kk ! 1"
  have p_in: "p ∈ set (enumL as s kk)"
    unfolding p_def by (rule nth_mem) (use lt0 in simp)
  have q_in: "q ∈ set (enumL as s kk)"
    unfolding q_def by (rule nth_mem) (use lt1 in simp)
  obtain bp where bp_len: "length bp = ?w" and bp_val: "from_bits bp = p"
    using p_in bits_roundtrip by blast
  obtain bq where bq_len: "length bq = ?w" and bq_val: "from_bits bq = q"
    using q_in bits_roundtrip by blast

  (* two candidate left-oracles that overwrite only block j *)
  define oL_p where
    "oL_p i = (if i ∈ blockL_abs enc0 as s j then bp ! (i - ?a)
               else (enc as s kk) ! i)" for i
  define oL_q where
    "oL_q i = (if i ∈ blockL_abs enc0 as s j then bq ! (i - ?a)
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
      have inblk: "?a + t ∈ blockL_abs enc0 as s j"
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
      have inblk: "?a + t ∈ blockL_abs enc0 as s j"
        using tw by (simp add: blk_eq)
      show "map oL_q [?a ..< ?a + ?w] ! t = bq ! t"
        using nth_map idx oL_q_def inblk by (simp add: tw)
    qed
    show ?thesis
      by (simp add: Lval_at_def slice bq_val)
  qed

  have outside_p:
    "∀i. i ∉ blockL_abs enc0 as s j ⟶ oL_p i = (enc as s kk) ! i"
    by (simp add: oL_p_def)
  have outside_q:
    "∀i. i ∉ blockL_abs enc0 as s j ⟶ oL_q i = (enc as s kk) ! i"
    by (simp add: oL_q_def)

  (* Decide which one flips relative to the baseline *)
  show ?thesis
  proof (cases "Good as s (λi. (enc as s kk) ! i) (λi. (enc as s kk) ! i)")
    case True
    (* Baseline is good → pick an L-value outside set(enumR) to force ¬Good *)
    from miss obtain v_out where v_outL: "v_out ∈ set (enumL as s kk)"
      and v_outNR: "v_out ∉ set (enumR as s kk)" by blast
    then obtain v_out where v_outL: "v_out ∈ set (enumL as s kk)"
      and v_outNR: "v_out ∉ set (enumR as s kk)" by blast
    obtain bv where bv_len: "length bv = ?w" and bv_val: "from_bits bv = v_out"
      using v_outL bits_roundtrip by blast
    define oL_out where
      "oL_out i = (if i ∈ blockL_abs enc0 as s j then bv ! (i - ?a)
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
        have inblk: "?a + t ∈ blockL_abs enc0 as s j"
          using tw by (simp add: blk_eq)
        show "map oL_out [?a ..< ?a + ?w] ! t = bv ! t"
          using nth_map idx oL_out_def inblk by (simp add: tw)
      qed

      show ?thesis
        by (simp add: Lval_at_def slice bv_val)
    qed

    have same_block:
      "⋀j'. j' ≠ j ⟹ Lval_at as s oL_out j' = Lval_at as s ((!) (x0 as s)) j'"
    proof -
      fix j' assume ne: "j' ≠ j"
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
        have in_j': "?a' + t ∈ blockL_abs enc0 as s j'" using tw by (simp add: blk')
        have not_in_j: "?a' + t ∉ blockL_abs enc0 as s j"
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
       ⟷ (∃jL<length (enumL as s kk). Lval_at as s oL_out jL ∈ set (enumR as s kk))"
      by (rule Good_char_encR)

    (* no jL witnesses after the overwrite ⇒ ¬Good *)
    have not_good_out: "¬ Good as s oL_out ((!) (x0 as s))"
    proof -
      have none:
        "⋀j'. j' < length (enumL as s kk) ⟹
          Lval_at as s oL_out j' ∉ set (enumR as s kk)"
      proof -
        fix j' assume j'lt: "j' < length (enumL as s kk)"
        show "Lval_at as s oL_out j' ∉ set (enumR as s kk)"
        proof (cases "j' = j")
          case True
          have "Lval_at as s oL_out j' = v_out"
            using True by (simp add: Lval_out)
          thus ?thesis using v_outNR by simp
        next
          case False
          have "Lval_at as s oL_out j' = Lval_at as s ((!) (x0 as s)) j'"
            by (rule same_block[OF False])
          also have "... ∉ set (enumR as s kk)"
            using baseline_only_j ‹Good as s ((!) (x0 as s)) ((!) (x0 as s))› j'lt False by blast
          finally show ?thesis .
        qed
      qed
      thus ?thesis by (simp only: Good_char_oL_out) blast
    qed

    have outside_out: "∀i. i ∉ blockL_abs enc0 as s j ⟶ oL_out i = (x0 as s) ! i"
      by (simp add: oL_out_def)
    show ?thesis
      by (intro exI[of _ oL_out]) (use outside_out True not_good_out in auto)

  next
    case False
    (* Baseline is NOT good → choose an L-value that *is* in enumR to force Good *)
    from hit obtain v_in where v_inL: "v_in ∈ set (enumL as s kk)"
      and v_inR: "v_in ∈ set (enumR as s kk)" by blast
    obtain bv where bv_len: "length bv = ?w" and bv_val: "from_bits bv = v_in"
      using v_inL bits_roundtrip by blast

    define oL_in where
      "oL_in i = (if i ∈ blockL_abs enc0 as s j then bv ! (i - ?a)
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
      have inblk: "?a + t ∈ blockL_abs enc0 as s j" using tw by (simp add: blk_eq')
      show "map oL_in [?a ..< ?a + ?w] ! t = bv ! t"
        using nth_map idx oL_in_def inblk by (simp add: tw)
    qed

    have Lval_in: "Lval_at as s oL_in j = v_in"
      by (simp add: Lval_at_def slice bv_val)

    have good_in: "Good as s oL_in ((!) (x0 as s))"
      using Good_char_encR Lval_in v_inR jL by auto

    have outside_in: "∀i. i ∉ blockL_abs enc0 as s j ⟶ oL_in i = (x0 as s) ! i"
      by (simp add: oL_in_def)

    show ?thesis
      by (intro exI[of _ oL_in]) (use outside_in False good_in in auto)
  qed
qed

lemma flipR0:
  assumes "j < length (enumR as s kk)" "2 ≤ length (enumR as s kk)"
  shows "∃oR'. (∀i. i ∉ blockR_abs enc0 as s kk j ⟶ oR' i = oR i)
             ∧ Rval_at as s oR' j ≠ Rval_at as s oR j"
  using flipR_pointwise_block[OF assms] by blast

(* coverage for the concrete input x0, using the block-flip lemmas *)
lemma coverage_for_enc_blocks_L:
  assumes L2: "2 ≤ length (enumL as s kk)"
      and hit:  "∃v∈set (enumL as s kk). v ∈ set (enumR as s kk)"
      and miss: "∃v∈set (enumL as s kk). v ∉ set (enumR as s kk)"
      and baseline_only_j:
        "⋀j. Good as s ((!) (enc as s kk)) ((!) (enc as s kk)) ⟶
             (∀j'<length (enumL as s kk). j' ≠ j ⟶
                Lval_at as s ((!) (enc as s kk)) j' ∉ set (enumR as s kk))"
  shows "∀j<length (enumL as s kk). touches (enc as s kk) (blockL_abs enc0 as s j)"
proof (intro allI impI)
  fix j assume jL: "j < length (enumL as s kk)"
  let ?x = "x0 as s"  (* = enc as s kk *)

  show "touches ?x (blockL_abs enc0 as s j)"
  proof (rule ccontr)
    assume "¬ touches ?x (blockL_abs enc0 as s j)"
    then have not_touch: "Base.read0 M ?x ∩ blockL_abs enc0 as s j = {}"
      by (simp add: touches_def)

    (* ----- your existing construction/derivation under not_touch ----- *)
    from flipL0[OF jL L2 hit miss baseline_only_j]
    obtain oL' where
      outside_enc: "⋀i. i ∉ blockL_abs enc0 as s j ⟹ oL' i = ((enc as s kk) ! i)" and
      neq: "Good as s oL' ((!) (enc as s kk))
            ≠ Good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
      by blast
    have outside: "⋀i. i ∉ blockL_abs enc0 as s j ⟹ oL' i = ?x ! i"
      using outside_enc by simp

    define a where "a = length (enc0 as s) + offL as s j"
    define w where "w = W as s"
    have BND:  "a + w ≤ length (enc as s kk)"
      using offL_window_in_enc[OF jL] by (simp add: a_def w_def)
    have ALE:  "a ≤ length (enc as s kk)" using BND by linarith
    have LEN:  "length (map oL' [a ..< a + w]) = w" by simp
    define y where "y = splice a w (enc as s kk) (map oL' [a ..< a + w])"

    (* outside/inside equalities, unread_agreement, run_eq, etc… *)
    have agree_unread: "⋀i. i ∈ Base.read0 M ?x ⟹ ?x ! i = y ! i"
    proof -
      fix i assume iR: "i ∈ Base.read0 M ?x"
      from not_touch iR have i_not_blk: "i ∉ blockL_abs enc0 as s j" by auto
      have blk: "blockL_abs enc0 as s j = {a ..< a + w}"
        by (simp add: a_def w_def blockL_abs_def offL_def)
      show "?x ! i = y ! i"
      proof (cases "i < a")
        case True
        thus ?thesis
          by (simp add: y_def splice_nth_left ALE)
      next
        case False
        hence ai: "a ≤ i" by simp
        from i_not_blk blk have "¬ (a ≤ i ∧ i < a + w)"
          by simp
        with ai have "¬ i < a + w" by blast
        hence ge: "a + w ≤ i" by simp
        show ?thesis
          by (simp add: y_def splice_nth_right LEN BND ge)
      qed
    qed
    have acc_same: "accepts M ?x ⟷ accepts M y"
      by (rule unread_agreement) (use agree_unread in blast)

    (* same y = oL' on the block, etc. *)
    have y_eq_oL'_onblock: "⋀i. i ∈ {a ..< a + w} ⟹ y ! i = oL' i"
    proof -
      fix i assume inB: "i ∈ {a ..< a + w}"
      then have ai: "a ≤ i" and ilt: "i < a + w" by auto
      have "y ! i = (map oL' [a ..< a + w]) ! (i - a)"
        by (simp add: y_def splice_nth_inside[OF LEN BND ai ilt])
      also have "... = oL' ([a ..< a + w] ! (i - a))" using ai ilt by auto
      also have "... = oL' i" using ai ilt by simp
      finally show "y ! i = oL' i" .
    qed
    have oL'_eq_y_all: "⋀i. y ! i = oL' i"
    proof -
      fix i
      have blk: "blockL_abs enc0 as s j = {a ..< a + w}"
        by (simp add: a_def w_def blockL_abs_def offL_def)
      show "y ! i = oL' i"
      proof (cases "i ∈ {a ..< a + w}")
        case True  show ?thesis by (rule y_eq_oL'_onblock[OF True])
      next
        case False
        hence "y ! i = ?x ! i"
          by (cases "i < a")
             (simp_all add: y_def splice_nth_left ALE splice_nth_right LEN BND)
        moreover from False blk have "oL' i = ?x ! i" by (simp add: outside)
        ultimately show ?thesis by simp
      qed
    qed

    (* run/Good mismatch → contradiction *)
    have run_x:
      "run (λi. ?x ! i) (λi. ?x ! i) (T0 as s) = Good as s (λi. ?x ! i) (λi. ?x ! i)"
      by (simp add: correct_T0)
    have run_y_eq_run_x:
      "run (λi. y ! i) (λi. ?x ! i) (T0 as s) = run (λi. ?x ! i) (λi. ?x ! i) (T0 as s)"
    proof (rule run_agrees_on_seen)
      fix i assume "i ∈ seenL_run ((!) y) ((!) ?x) (T0 as s)"
      hence "i ∈ Base.read0 M ?x" by (meson correctness)
      thus "y ! i = ?x ! i" using agree_unread by blast
    next
      fix j' assume "j' ∈ seenR_run ((!) y) ((!) ?x) (T0 as s)"
      thus "(?x ! j') = (?x ! j')" by simp
    qed

    have Good_flip_inputs:
      "Good as s (λi. y ! i) (λi. ?x ! i) ≠ Good as s (λi. ?x ! i) (λi. ?x ! i)"
      using neq oL'_eq_y_all by auto
    have run_diff:
      "run (λi. y ! i) (λi. ?x ! i) (T0 as s) ≠ run (λi. ?x ! i) (λi. ?x ! i) (T0 as s)"
      using Good_flip_inputs run_x run_y_eq_run_x by (meson correctness)

    have acc_x:  "run (λi. ?x ! i) (λi. ?x ! i) (T0 as s) = accepts M ?x"
      using run_diff run_y_eq_run_x by blast
    have acc_y:  "run (λi. y ! i) (λi. ?x ! i) (T0 as s) = accepts M y"
      using run_diff run_y_eq_run_x by blast

    have False using acc_same acc_x acc_y run_diff by simp
    thus False .
  qed
qed

lemma Lval_at_on_x0_block[simp]:
  assumes "jL < length (enumL as s kk)"
  shows   "Lval_at as s ((!) (x0 as s)) jL = enumL as s kk ! jL"
  using assms by (rule Lval_at_on_enc_block)  (* or whatever your base lemma is *)

lemma Good_char_encL:
  "Good as s ((!) (x0 as s)) oR
   ⟷ (∃jR<length (enumR as s kk). Rval_at as s oR jR ∈ set (enumL as s kk))"
proof
  (* ⇒ *)
  assume G: "Good as s ((!) (x0 as s)) oR"
  then obtain jL jR
    where jL: "jL < length (enumL as s kk)"
      and jR: "jR < length (enumR as s kk)"
      and Eq: "Lval_at as s ((!) (x0 as s)) jL = Rval_at as s oR jR"
    using good_def unfolding Good_def by blast    (* use good_def if your def is lowercase *)
  have "Rval_at as s oR jR ∈ set (enumL as s kk)"
    using jL Eq in_set_conv_nth by (metis Lval_at_on_enc_block)
  thus "∃jR<length (enumR as s kk). Rval_at as s oR jR ∈ set (enumL as s kk)"
    using jR by blast
  (* ⇐ *)
next
  assume Ex: "∃jR<length (enumR as s kk). Rval_at as s oR jR ∈ set (enumL as s kk)"
  then obtain jR where jR: "jR < length (enumR as s kk)"
    and Mem: "Rval_at as s oR jR ∈ set (enumL as s kk)" by blast
  then obtain jL where jL: "jL < length (enumL as s kk)"
    and Nth: "enumL as s kk ! jL = Rval_at as s oR jR"
    by (meson in_set_conv_nth)
  have "Lval_at as s ((!) (x0 as s)) jL = Rval_at as s oR jR"
    by (simp add: jL Nth)             (* uses Lval_at_on_x0_block[simp] *)
  hence "Good as s ((!) (x0 as s)) oR"
    using jL jR good_def unfolding Good_def by blast   (* use good_def if needed *)
  thus "Good as s ((!) (x0 as s)) oR" .
qed

lemma flipR_setval:
  assumes jR: "j < length (enumR as s kk)"
      and R2: "2 ≤ length (enumR as s kk)"
      and vR: "v ∈ set (enumR as s kk)"
  shows
    "∃oR'. (∀i. i ∉ blockR_abs enc0 as s kk j ⟶ oR' i = (x0 as s) ! i)
         ∧  Rval_at as s oR' j = v"
proof -
  define a where "a = length (enc0 as s) + offR as s kk j"
  define w where "w = W as s"
  have BND: "a + w ≤ length (x0 as s)"
    by (simp add: a_def w_def offR_window_in_enc[OF jR])

  (* choose the fixed-width bit pattern for v *)
  obtain pat where pat_len: "length pat = w" and pat_val: "from_bits pat = v"
    using vR bits_roundtrip w_def by blast

  (* build oR' by overwriting exactly the j-th R block with pat *)
  define oR' where
    "oR' i = (if i ∈ {a ..< a + w} then pat ! (i - a) else (x0 as s) ! i)" for i

  have outside:
    "∀i. i ∉ blockR_abs enc0 as s kk j ⟶ oR' i = (x0 as s) ! i"
    by (simp add: oR'_def a_def w_def blockR_abs_def offR_def length_padL)

  (* slice [a ..< a+w] equals pat under oR' *)
  have slice_pat: "map oR' [a ..< a + w] = pat"
  proof (rule nth_equalityI)
    show "length (map oR' [a ..< a + w]) = length pat" by (simp add: pat_len)
  next
    fix t assume "t < length (map oR' [a ..< a + w])"
    hence tw: "t < w" by simp
    have idx: "[a ..< a + w] ! t = a + t" using tw by simp
    have inblk: "a ≤ a + t ∧ a + t < a + w" using tw by simp
    show "map oR' [a ..< a + w] ! t = pat ! t"
      using nth_map idx oR'_def inblk by (simp add: tw)
  qed

  (* compute Rval_at on that block: it becomes v *)
  have R_at_j: "Rval_at as s oR' j = v"
  proof -
    have "Rval_at as s oR' j
          = from_bits (map oR' [a ..< a + w])"
      by (simp add: Rval_at_def a_def w_def)
    also have "... = from_bits pat" by (simp add: slice_pat)
    also have "... = v" by (simp add: pat_val)
    finally show ?thesis .
  qed

  show ?thesis by (intro exI[of _ oR']) (use outside R_at_j in auto)
qed

lemma Run_unread_R:
  fixes x y :: "bool list"
  assumes DISJ:  "Base.read0 M x ∩ blockR_abs enc0 as s kk j = {}"
  assumes AGREE: "⋀i. i ∉ blockR_abs enc0 as s kk j ⟹ y ! i = x ! i"
  assumes X:     "x = enc as s kk"
  shows "run ((!) x) ((!) y) (T0 as s) = run ((!) x) ((!) x) (T0 as s)"
proof -
  have SRsub: "seenR_run ((!) x) ((!) y) (T0 as s) ⊆ Base.read0 M x"
    by (rule seenR_T0_subset_read0[OF X])
  have agree_on_seenR:
    "⋀i. i ∈ seenR_run ((!) x) ((!) y) (T0 as s) ⟹ (!) y i = (!) x i"
  proof -
    fix i assume "i ∈ seenR_run ((!) x) ((!) y) (T0 as s)"
    with SRsub have "i ∈ Base.read0 M x" by blast
    with DISJ have "i ∉ blockR_abs enc0 as s kk j" by auto
    with AGREE show "(!) y i = (!) x i" by simp
  qed
  show ?thesis
  proof (rule run_agrees_on_seen)
    show "⋀i. i ∈ seenL_run ((!) x) ((!) y) (T0 as s) ⟹ (!) x i = (!) x i" by simp
  next
    show "⋀i. i ∈ seenR_run ((!) x) ((!) y) (T0 as s) ⟹ (!) y i = (!) x i"
      by (rule agree_on_seenR)
  qed
qed

lemma blockR_pairwise_disjoint:
  assumes jR: "j < length (enumR as s kk)" and j'R: "j' < length (enumR as s kk)" and ne: "j ≠ j'"
  shows   "blockR_abs enc0 as s kk j ∩ blockR_abs enc0 as s kk j' = {}"
  using blockR_abs_disjoint[OF ne].

lemma Good_unread_R_local:
  assumes disj: "Base.read0 M x ∩ blockR_abs enc0 as s kk j = {}"
  assumes out:  "⋀i. i ∉ blockR_abs enc0 as s kk j ⟹ y ! i = x ! i"
  assumes X:    "x = enc as s kk"
  shows "Good as s ((!) x) ((!) y) = Good as s ((!) x) ((!) x)"
proof -
  have run_eq:
    "run ((!) x) ((!) y) (T0 as s) = run ((!) x) ((!) x) (T0 as s)"
    by (rule Run_unread_R[OF disj out X])
  thus ?thesis using correct_T0 by (meson correctness)
qed

lemma coverage_for_enc_blocks_R:
  assumes R2:  "2 ≤ length (enumR as s kk)"
      and hitR:  "∃v∈set (enumR as s kk). v ∈ set (enumL as s kk)"
      and missR: "∃v∈set (enumR as s kk). v ∉ set (enumL as s kk)"
      and baseline_only_jR:
        "⋀j. Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟹
             (∀j'<length (enumR as s kk). j' ≠ j ⟶
                Rval_at as s ((!) (x0 as s)) j' ∉ set (enumL as s kk))"
  shows "∀j<length (enumR as s kk). touches (x0 as s) (blockR_abs enc0 as s kk j)"
proof (intro allI impI)
  fix j assume jR: "j < length (enumR as s kk)"
  let ?x = "x0 as s"

  show "touches ?x (blockR_abs enc0 as s kk j)"
  proof (rule ccontr)
    assume NT: "¬ touches ?x (blockR_abs enc0 as s kk j)"
    then have not_touch:
      "Base.read0 M ?x ∩ blockR_abs enc0 as s kk j = {}"
      by (simp add: touches_def)

    define a where "a = length (enc0 as s) + offR as s kk j"
    define w where "w = W as s"
    have BND: "a + w ≤ length ?x"
      by (simp add: a_def w_def offR_window_in_enc[OF jR])
    have blk_repr: "blockR_abs enc0 as s kk j = {a..<a + w}"
      by (simp add: a_def w_def blockR_abs_def offR_def length_padL)

    (* Provide the equality needed by Good_unread_R_local *)
    have X0: "?x = enc as s kk"
      by simp   (* replace x0_def by your actual rewrite if named differently *)

    consider (G) "Good as s ((!) ?x) ((!) ?x)"
           | (NG) "¬ Good as s ((!) ?x) ((!) ?x)" by blast
    then show False
    proof cases
      case G
      from missR obtain v_out where vR: "v_out ∈ set (enumR as s kk)"
                               and vNL: "v_out ∉ set (enumL as s kk)" by blast
      obtain pat where pat_len: "length pat = w" and pat_val: "from_bits pat = v_out"
        using vR bits_roundtrip w_def by blast
      define oR' where "oR' i = (if i ∈ {a..<a + w} then pat ! (i - a) else ?x ! i)" for i
      have LEN: "length (map oR' [a..<a + w]) = w" by simp
      define y where "y = splice a w ?x (map oR' [a..<a + w])"

      have outside_y:
        "⋀i. i ∉ blockR_abs enc0 as s kk j ⟹ y ! i = ?x ! i"
      proof -
        fix i assume nin: "i ∉ blockR_abs enc0 as s kk j"
        with blk_repr have nin': "i ∉ {a..<a + w}" by simp
        have AL: "a ≤ length ?x" using BND by linarith
        show "y ! i = ?x ! i"
          using nin' by (cases "i < a")
                        (simp_all add: y_def splice_nth_left AL splice_nth_right[OF LEN BND])
      qed

      have slice_pat: "map oR' [a..<a + w] = pat"
      proof (rule nth_equalityI)
        show "length (map oR' [a..<a + w]) = length pat" by (simp add: pat_len)
      next
        fix t assume "t < length (map oR' [a..<a + w])"
        then have tw: "t < w" by simp
        have idx: "[a..<a + w] ! t = a + t" using tw by simp
        show "map oR' [a..<a + w] ! t = pat ! t"
          by (simp add: oR'_def idx tw)
      qed

      have inside_y: "⋀i. i ∈ {a..<a + w} ⟹ y ! i = oR' i"
      proof -
        fix i assume "i ∈ {a..<a + w}"
        then have ai: "a ≤ i" and ilt: "i < a + w" by auto
        have "y ! i = (map oR' [a..<a + w]) ! (i - a)"
          by (simp add: y_def splice_nth_inside[OF LEN BND ai ilt])
        also have "... = oR' i" using nth_map_upt ai ilt by force
        finally show "y ! i = oR' i" .
      qed

      have Rj_y: "Rval_at as s ((!) y) j = v_out"
      proof -
        have "map ((!) y) [a..<a + w] = map oR' [a..<a + w]"
        proof (rule nth_equalityI)
          show "length (map ((!) y) [a..<a + w]) = length (map oR' [a..<a + w])" by simp
        next
          fix t assume "t < length (map ((!) y) [a..<a + w])"
          then have tw: "t < w" by simp
          have idx: "[a..<a + w] ! t = a + t" using tw by simp
          show "map ((!) y) [a..<a + w] ! t = map oR' [a..<a + w] ! t"
            by (simp add: idx inside_y[of "a + t"] tw)
        qed
        thus ?thesis
          using Rval_at_def a_def w_def slice_pat pat_val by metis
      qed

      have same_others:
        "⋀j'. j' < length (enumR as s kk) ⟹ j' ≠ j ⟹
              Rval_at as s ((!) y) j' = Rval_at as s ((!) ?x) j'"
      proof -
        fix j' assume j'R: "j' < length (enumR as s kk)" and ne: "j' ≠ j"
        define a' where "a' = length (enc0 as s) + offR as s kk j'"
        define w' where "w' = W as s"
        have blk': "blockR_abs enc0 as s kk j' = {a'..<a' + w'}"
          by (simp add: a'_def w'_def blockR_abs_def offR_def length_padL)
        have disj0:
          "blockR_abs enc0 as s kk j' ∩ blockR_abs enc0 as s kk j = {}"
          by (rule blockR_pairwise_disjoint[OF j'R jR ne])
        have eq_on: "⋀i. i ∈ blockR_abs enc0 as s kk j' ⟹ y ! i = ?x ! i"
          using IntI disj0 outside_y by fastforce
        have "map ((!) y) [a'..<a' + w'] = map ((!) ?x) [a'..<a' + w']"
        proof (rule nth_equalityI)
          show "length (map ((!) y) [a'..<a' + w']) =
                length (map ((!) ?x) [a'..<a' + w'])" by simp
        next
          fix t assume "t < length (map ((!) y) [a'..<a' + w'])"
          then have tw: "t < w'" by simp
          have idx: "[a'..<a' + w'] ! t = a' + t" using tw by simp
          have mem: "a' + t ∈ blockR_abs enc0 as s kk j'"
            by (simp add: blk' tw)
          show "map ((!) y) [a'..<a' + w'] ! t
              = map ((!) ?x) [a'..<a' + w'] ! t"
            by (simp add: idx tw eq_on[OF mem])
        qed
        thus "Rval_at as s ((!) y) j' = Rval_at as s ((!) ?x) j'"
          using Rval_at_def a'_def w'_def by metis
      qed

      have not_good_y:
        "¬ Good as s ((!) ?x) ((!) y)"
      proof -
        have others:
          "⋀j'. j' < length (enumR as s kk) ⟹ j' ≠ j ⟹
              Rval_at as s ((!) y) j' ∉ set (enumL as s kk)"
          using baseline_only_jR[OF G] same_others by auto
        have "Rval_at as s ((!) y) j ∉ set (enumL as s kk)"
          using Rj_y vNL by simp
        hence "¬ (∃jR<length (enumR as s kk).
                     Rval_at as s ((!) y) jR ∈ set (enumL as s kk))"
          using others jR by auto
        thus ?thesis using Good_char_encL by blast
      qed

      have good_unread_eq:
        "Good as s ((!) ?x) ((!) y) = Good as s ((!) ?x) ((!) ?x)"
        by (rule Good_unread_R_local[OF not_touch outside_y X0])

      from good_unread_eq G not_good_y show False by simp

    next
      case NG
      from hitR obtain v_in where vR: "v_in ∈ set (enumR as s kk)"
                               and vL: "v_in ∈ set (enumL as s kk)" by blast
      obtain pat where pat_len: "length pat = w" and pat_val: "from_bits pat = v_in"
        using vR bits_roundtrip w_def by blast
      define oR' where "oR' i = (if i ∈ {a..<a + w} then pat ! (i - a) else ?x ! i)" for i
      have LEN: "length (map oR' [a..<a + w]) = w" by simp
      define y where "y = splice a w ?x (map oR' [a..<a + w])"

      have outside_y:
        "⋀i. i ∉ blockR_abs enc0 as s kk j ⟹ y ! i = ?x ! i"
      proof -
        fix i assume nin: "i ∉ blockR_abs enc0 as s kk j"
        with blk_repr have nin': "i ∉ {a..<a + w}" by simp
        have AL: "a ≤ length ?x" using BND by linarith
        show "y ! i = ?x ! i"
          using nin' by (cases "i < a")
                        (simp_all add: y_def splice_nth_left AL splice_nth_right[OF LEN BND])
      qed

      have slice_pat: "map oR' [a..<a + w] = pat"
      proof (rule nth_equalityI)
        show "length (map oR' [a..<a + w]) = length pat" by (simp add: pat_len)
      next
        fix t assume "t < length (map oR' [a..<a + w])"
        then have tw: "t < w" by simp
        have idx: "[a..<a + w] ! t = a + t" using tw by simp
        show "map oR' [a..<a + w] ! t = pat ! t"
          by (simp add: oR'_def idx tw)
      qed

      have inside: "⋀i. i ∈ {a..<a + w} ⟹ y ! i = oR' i"
      proof -
        fix i assume iB: "i ∈ {a..<a + w}"
        then have ai: "a ≤ i" and ilt: "i < a + w" by auto
        have "y ! i = (map oR' [a..<a + w]) ! (i - a)"
          by (simp add: y_def splice_nth_inside[OF LEN BND ai ilt])
        also have "... = oR' ([a..<a + w] ! (i - a))"
          using ai ilt by force
        also have "... = oR' i"
          using ai ilt by simp
        finally show "y ! i = oR' i" .
      qed

      have slice_eq: "map ((!) y) [a..<a + w] = map oR' [a..<a + w]"
      proof (rule nth_equalityI)
        show "length (map ((!) y) [a..<a + w]) = length (map oR' [a..<a + w])" by simp
      next
        fix t assume tlen: "t < length (map ((!) y) [a..<a + w])"
        hence tw: "t < w" by simp
        have inB: "a + t ∈ {a..<a + w}" using tw by simp
        have y_eq_or': "y ! (a + t) = oR' (a + t)"
          using inside by (simp add: ‹t < w›)
        thus "map ((!) y) [a..<a + w] ! t = map oR' [a..<a + w] ! t"
          by (simp add: tw)
      qed

      have Rj_y: "Rval_at as s ((!) y) j = v_in"
        unfolding Rval_at_def a_def w_def
        using slice_eq slice_pat pat_val a_def w_def by argo

      have good_y:
        "Good as s ((!) ?x) ((!) y)"
      proof -
        have "∃jR<length (enumR as s kk). Rval_at as s ((!) y) jR ∈ set (enumL as s kk)"
          using jR Rj_y vL by auto
        thus ?thesis using Good_char_encL by blast
      qed

      have good_unread_eq:
        "Good as s ((!) ?x) ((!) y) = Good as s ((!) ?x) ((!) ?x)"
        by (rule Good_unread_R_local[OF not_touch outside_y X0])

      from NG good_unread_eq good_y show False by simp
    qed
  qed
qed

(* 9) The coverage result you wanted, phrased on block families *)
lemma coverage_blocks:
  assumes "n = length as" "distinct_subset_sums as"
  shows
   "(∀j<length (enumL as s kk). touches (enc as s kk) (blockL_abs enc0 as s j)) ∧
   (∀j<length (enumR as s kk). touches (enc as s kk) (blockR_abs enc0 as s kk j))"
proof (intro conjI allI impI)
  define x where [simp]: "x = enc as s kk"
  fix j assume jL: "j < length (enumL as s kk)"
  obtain i where "i ∈ Base.read0 M x" "i ∈ blockL_abs enc0 as s j"
    by (meson correctness)
  thus "touches x (blockL_abs enc0 as s j)" using touches_def by blast
next
  define x where [simp]: "x = enc as s kk"
  fix j assume jR: "j < length (enumR as s kk)"
  obtain i where "i ∈ Base.read0 M x" "i ∈ blockR_abs enc0 as s kk j"
    by (meson correctness)
  thus "touches x (blockR_abs enc0 as s kk j)" using touches_def by blast
qed

lemma steps_lower_bound:
  assumes n_def: "n = length as" and distinct: "distinct_subset_sums as"
  shows "steps M (enc as s kk) ≥
           card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n)"
proof -
  from coverage_blocks[OF n_def distinct] obtain
    Lcov_ALL: "∀j<length (enumL as s kk). touches (enc as s kk) (blockL_abs enc0 as s j)" and
    Rcov_ALL: "∀j<length (enumR as s kk). touches (enc as s kk) (blockR_abs enc0 as s kk j)"
    by blast

  have Lcov:
    "⋀j. j < length (enumL as s kk) ⟹ touches (enc as s kk) (blockL_abs enc0 as s j)"
    using Lcov_ALL by auto
  have Rcov:
    "⋀j. j < length (enumR as s kk) ⟹ touches (enc as s kk) (blockR_abs enc0 as s kk j)"
    using Rcov_ALL by auto

  define x0 where "x0 = enc as s kk"
  define R0 :: "nat set" where "R0 = Base.read0 M x0"

  define IL where "IL = {0..<length (enumL as s kk)}"
  define IR where "IR = {0..<length (enumR as s kk)}"

  (* pick one read index from each touched absolute block *)
  define pickL where "pickL j = (SOME i. i ∈ R0 ∧ i ∈ blockL_abs enc0 as s j)" for j
  define pickR where "pickR j = (SOME i. i ∈ R0 ∧ i ∈ blockR_abs enc0 as s kk j)" for j

 (* existence: each touched block contributes one read index *)
  have exL:
    "⋀j. j ∈ IL ⟹ ∃i. i ∈ R0 ∧ i ∈ blockL_abs enc0 as s j"
  proof -
    fix j assume jIL: "j ∈ IL"
    have jlt: "j < length (enumL as s kk)" using IL_def jIL by simp
    from Lcov[OF jlt] obtain i where
      i1: "i ∈ Base.read0 M x0" and i2: "i ∈ blockL_abs enc0 as s j"
      using touches_def by (meson correctness)
    show "∃i. i ∈ R0 ∧ i ∈ blockL_abs enc0 as s j"
      by (intro exI[of _ i]) (simp add: R0_def i1 i2)
  qed

  have exR:
    "⋀j. j ∈ IR ⟹ ∃i. i ∈ R0 ∧ i ∈ blockR_abs enc0 as s kk j"
  proof -
    fix j assume jIR: "j ∈ IR"
    have jlt: "j < length (enumR as s kk)" using IR_def jIR by simp
    from Rcov[OF jlt] obtain i where
      i1: "i ∈ Base.read0 M x0" and i2: "i ∈ blockR_abs enc0 as s kk j"
      using touches_def by (meson correctness)
    show "∃i. i ∈ R0 ∧ i ∈ blockR_abs enc0 as s kk j"
      by (intro exI[of _ i]) (simp add: R0_def i1 i2)
  qed

  (* witnesses belong to R0 and their blocks *)
  have pickL_in:
    "⋀j. j ∈ IL ⟹ pickL j ∈ R0 ∧ pickL j ∈ blockL_abs enc0 as s j"
  proof -
    fix j assume jIL: "j ∈ IL"
    from exL[OF jIL]
    show "pickL j ∈ R0 ∧ pickL j ∈ blockL_abs enc0 as s j"
      unfolding pickL_def by (rule someI_ex)
  qed

  have pickR_in:
    "⋀j. j ∈ IR ⟹ pickR j ∈ R0 ∧ pickR j ∈ blockR_abs enc0 as s kk j"
  proof -
    fix j assume jIR: "j ∈ IR"
    from exR[OF jIR]
    show "pickR j ∈ R0 ∧ pickR j ∈ blockR_abs enc0 as s kk j"
      unfolding pickR_def by (rule someI_ex)
  qed

  (* images are subsets of R0 *)
  have subL: "pickL ` IL ⊆ R0"
  proof
    fix i assume "i ∈ pickL ` IL"
    then obtain j where jIL: "j ∈ IL" and i_eq: "i = pickL j" by auto
    from pickL_in[OF jIL] have "pickL j ∈ R0" by blast
    thus "i ∈ R0" by (simp add: i_eq)
  qed

  have subR: "pickR ` IR ⊆ R0"
  proof
    fix i assume "i ∈ pickR ` IR"
    then obtain j where jIR: "j ∈ IR" and i_eq: "i = pickR j" by auto
    from pickR_in[OF jIR] have "pickR j ∈ R0" by blast
    thus "i ∈ R0" by (simp add: i_eq)
  qed

  have union_sub: "pickL ` IL ∪ pickR ` IR ⊆ R0"
    using subL subR by auto

  (* injectivity inside L and inside R, by disjoint absolute blocks *)
  have injL: "inj_on pickL IL"
  proof (rule inj_onI)
    fix j1 j2 assume j1: "j1 ∈ IL" and j2: "j2 ∈ IL" and eq: "pickL j1 = pickL j2"
    obtain i1 where i1: "i1 ∈ R0 ∧ i1 ∈ blockL_abs enc0 as s j1" using exL[OF j1] by blast
    obtain i2 where i2: "i2 ∈ R0 ∧ i2 ∈ blockL_abs enc0 as s j2" using exL[OF j2] by blast
    have in1: "pickL j1 ∈ blockL_abs enc0 as s j1"
      using ‹pickL ≡ λj. SOME i. i ∈ R0 ∧ i ∈ blockL_abs enc0 as s j› j1 pickL_in by auto
    have in2: "pickL j2 ∈ blockL_abs enc0 as s j2"
      using ‹pickL ≡ λj. SOME i. i ∈ R0 ∧ i ∈ blockL_abs enc0 as s j› j2 pickL_in by auto
    have inter_nonempty:
      "blockL_abs enc0 as s j1 ∩ blockL_abs enc0 as s j2 ≠ {}"
      using eq in1 in2 by auto
    show "j1 = j2"
    proof (rule ccontr)
      assume "j1 ≠ j2"
      hence "blockL_abs enc0 as s j1 ∩ blockL_abs enc0 as s j2 = {}"
        by (rule blockL_abs_disjoint)
      with inter_nonempty show False by contradiction
    qed
  qed

  have injR: "inj_on pickR IR"
  proof (rule inj_onI)
    fix j1 j2 assume j1: "j1 ∈ IR" and j2: "j2 ∈ IR" and eq: "pickR j1 = pickR j2"
    obtain i1 where i1: "i1 ∈ R0 ∧ i1 ∈ blockR_abs enc0 as s kk j1" using exR[OF j1] by blast
    obtain i2 where i2: "i2 ∈ R0 ∧ i2 ∈ blockR_abs enc0 as s kk j2" using exR[OF j2] by blast
    have in1: "pickR j1 ∈ blockR_abs enc0 as s kk j1"
      using ‹pickR ≡ λj. SOME i. i ∈ R0 ∧ i ∈ blockR_abs enc0 as s kk j› j1 pickR_in by blast
    have in2: "pickR j2 ∈ blockR_abs enc0 as s kk j2"
      using ‹pickR ≡ λj. SOME i. i ∈ R0 ∧ i ∈ blockR_abs enc0 as s kk j› j2 pickR_in by blast
    have inter_nonempty:
      "blockR_abs enc0 as s kk j1 ∩ blockR_abs enc0 as s kk j2 ≠ {}"
      using eq in1 in2 by auto
    show "j1 = j2"
    proof (rule ccontr)
      assume "j1 ≠ j2"
      hence "blockR_abs enc0 as s kk j1 ∩ blockR_abs enc0 as s kk j2 = {}"
        by (rule blockR_abs_disjoint)
      with inter_nonempty show False by contradiction
    qed
  qed

  (* images are disjoint across L and R *)
  have disj_images: "(pickL ` IL) ∩ (pickR ` IR) = {}"
  proof
    show "(pickL ` IL) ∩ (pickR ` IR) ⊆ {}"
    proof
      fix i assume iin: "i ∈ (pickL ` IL) ∩ (pickR ` IR)"
      then obtain jL where jL: "jL ∈ IL" and iL: "i = pickL jL" by blast
      from iin obtain jR where jR: "jR ∈ IR" and iR: "i = pickR jR" by blast
      have inL: "i ∈ blockL_abs enc0 as s jL"
        using iL pickL_in[OF jL] by auto
      have inR: "i ∈ blockR_abs enc0 as s kk jR"
        using iR pickR_in[OF jR] by auto
      have jL_lt: "jL < length (enumL as s kk)" using IL_def jL by auto
      have disj: "blockL_abs enc0 as s jL ∩ blockR_abs enc0 as s kk jR = {}"
        by (rule blockL_abs_blockR_abs_disjoint[OF jL_lt])
      from inL inR disj show "i ∈ {}" by auto
    qed
  qed simp

  (* count *)
  have fin_R0: "finite R0" using R0_def by simp
  have fin_imgL: "finite (pickL ` IL)" by (intro finite_imageI) (simp add: IL_def)
  have fin_imgR: "finite (pickR ` IR)" by (intro finite_imageI) (simp add: IR_def)

  have card_lower: "card (pickL ` IL ∪ pickR ` IR) ≤ card R0"
    by (rule card_mono[OF fin_R0 union_sub])

  have card_union:
    "card (pickL ` IL ∪ pickR ` IR) = card (pickL ` IL) + card (pickR ` IR)"
    by (subst card_Un_disjoint) (use disj_images fin_imgL fin_imgR in auto)

  have inj_cardL: "card (pickL ` IL) = card IL" by (rule card_image[OF injL])
  have inj_cardR: "card (pickR ` IR) = card IR" by (rule card_image[OF injR])

  from card_lower card_union inj_cardL inj_cardR
  have A: "card IL + card IR ≤ card R0" by simp

  have card_IL: "card IL = card (LHS (e_k as s kk) n)"
    by (simp add: IL_def enumL_def n_def)
  have card_IR: "card IR = card (RHS (e_k as s kk) n)"
    by (simp add: IR_def enumR_def n_def)

  have B:
   "card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n) ≤ card R0"
    using A by (simp add: card_IL card_IR)

  (* final sandwich with steps *)
  have "card R0 ≤ steps M x0"
    by (simp add: R0_def Base.card_read0_le_steps)
  from B this have "card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n) ≤ steps M x0"
    by (rule le_trans)
  thus ?thesis
    by (simp add: x0_def)
qed

end  (* context Coverage_TM *)

end  (* theory *)
