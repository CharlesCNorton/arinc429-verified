(******************************************************************************)
(*                                                                            *)
(*              ARINC 429: Avionics Data Bus Word Format                      *)
(*                                                                            *)
(*     32-bit word encoding with label (octal), SDI, data field, SSM,         *)
(*     and odd parity per ARINC Specification 429. Proves encoding/           *)
(*     decoding roundtrip, parity correctness, and label-space partition.     *)
(*                                                                            *)
(*     "Simplicity is the ultimate sophistication."                           *)
(*     - Leonardo da Vinci                                                    *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: March 16, 2026                                                   *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith Bool Lia List PeanoNat.

Local Open Scope nat_scope.

Import ListNotations.

Inductive arinc_429_revision :=
| arinc_429_part1_supp17.

Definition pinned_revision : arinc_429_revision :=
  arinc_429_part1_supp17.

Inductive spec_clause :=
| clause_word_format_32_bit
| clause_label_field_bits_1_8
| clause_sdi_field_bits_9_10
| clause_data_field_bits_11_29
| clause_ssm_field_bits_30_31
| clause_parity_bit_32_odd
| clause_label_octal_presentation.

Inductive development_item :=
| item_word_layout
| item_payload_encoding
| item_payload_decoding
| item_odd_parity_digit
| item_label_octal_conversion.

Definition traced_clauses (item : development_item) : list spec_clause :=
  match item with
  | item_word_layout =>
      [ clause_word_format_32_bit;
        clause_label_field_bits_1_8;
        clause_sdi_field_bits_9_10;
        clause_data_field_bits_11_29;
        clause_ssm_field_bits_30_31;
        clause_parity_bit_32_odd ]
  | item_payload_encoding =>
      [ clause_label_field_bits_1_8;
        clause_sdi_field_bits_9_10;
        clause_data_field_bits_11_29;
        clause_ssm_field_bits_30_31;
        clause_parity_bit_32_odd ]
  | item_payload_decoding =>
      [ clause_label_field_bits_1_8;
        clause_sdi_field_bits_9_10;
        clause_data_field_bits_11_29;
        clause_ssm_field_bits_30_31 ]
  | item_odd_parity_digit =>
      [ clause_parity_bit_32_odd ]
  | item_label_octal_conversion =>
      [ clause_label_field_bits_1_8;
        clause_label_octal_presentation ]
  end.

Definition current_scope : list development_item :=
  [ item_word_layout;
    item_payload_encoding;
    item_payload_decoding;
    item_odd_parity_digit;
    item_label_octal_conversion ].

Definition trace_entry_well_formed (item : development_item) : Prop :=
  traced_clauses item <> [].

Definition current_scope_fully_traced : Prop :=
  Forall trace_entry_well_formed current_scope.

Lemma pinned_revision_is_fixed :
  pinned_revision = arinc_429_part1_supp17.
Proof.
  reflexivity.
Qed.

Lemma current_scope_fully_traced_proof :
  current_scope_fully_traced.
Proof.
  unfold current_scope_fully_traced, current_scope, trace_entry_well_formed.
  repeat constructor; discriminate.
Qed.

Fixpoint pow2 (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => 2 * pow2 n'
  end.

Definition word_width : nat := 32.
Definition payload_width : nat := 31.

Definition label_offset : nat := 0.
Definition label_width : nat := 8.

Definition sdi_offset : nat := 8.
Definition sdi_width : nat := 2.

Definition data_offset : nat := 10.
Definition data_width : nat := 19.

Definition ssm_offset : nat := 29.
Definition ssm_width : nat := 2.

Definition parity_offset : nat := 31.
Definition parity_width : nat := 1.

Definition label_bound : nat := pow2 label_width.
Definition sdi_bound : nat := pow2 sdi_width.
Definition data_bound : nat := pow2 data_width.
Definition ssm_bound : nat := pow2 ssm_width.

Definition parity_weight : nat := pow2 payload_width.
Definition word_bound : nat := 2 * parity_weight.

Record word32 := {
  word32_unsigned : nat;
  word32_range : word32_unsigned < word_bound;
}.

Definition nat_of_word32 (word : word32) : nat :=
  word32_unsigned word.

Definition word32_of_nat (word : nat) (Hword : word < word_bound) : word32 :=
  {| word32_unsigned := word; word32_range := Hword |}.

Record fields := {
  label : nat;
  sdi : nat;
  data : nat;
  ssm : nat;
}.

Definition fields_valid (f : fields) : Prop :=
  label f < label_bound /\
  sdi f < sdi_bound /\
  data f < data_bound /\
  ssm f < ssm_bound.

Definition in_bit_range (offset width bit : nat) : Prop :=
  offset <= bit < offset + width.

Definition label_bit (bit : nat) : Prop :=
  in_bit_range label_offset label_width bit.

Definition sdi_bit (bit : nat) : Prop :=
  in_bit_range sdi_offset sdi_width bit.

Definition data_bit (bit : nat) : Prop :=
  in_bit_range data_offset data_width bit.

Definition ssm_bit (bit : nat) : Prop :=
  in_bit_range ssm_offset ssm_width bit.

Definition parity_bit (bit : nat) : Prop :=
  in_bit_range parity_offset parity_width bit.

Definition bit_mask (width : nat) : nat :=
  pow2 width - 1.

Definition field_mask (offset width : nat) : nat :=
  pow2 offset * bit_mask width.

Definition extract_bits (value offset width : nat) : nat :=
  (value / pow2 offset) mod pow2 width.

Definition insert_bits (value offset field : nat) : nat :=
  value + pow2 offset * field.

Definition bit_at (value bit : nat) : nat :=
  extract_bits value bit 1.

Definition wire_bit_index (position : nat) : nat :=
  if position <? label_width then label_width - 1 - position else position.

Definition wire_bit (word position : nat) : nat :=
  extract_bits word (wire_bit_index position) 1.

Definition payload (f : fields) : nat :=
  label f
    + label_bound
        * (sdi f
           + sdi_bound
               * (data f + data_bound * ssm f)).

Fixpoint bitcount_low (width value : nat) : nat :=
  match width with
  | 0 => 0
  | S width' => value mod 2 + bitcount_low width' (value / 2)
  end.

Definition odd_population (width value : nat) : bool :=
  Nat.odd (bitcount_low width value).

Definition expected_parity_digit_from_payload (value : nat) : nat :=
  if odd_population payload_width value then 0 else 1.

Definition expected_parity_digit (f : fields) : nat :=
  expected_parity_digit_from_payload (payload f).

Definition encode (f : fields) : nat :=
  payload f + parity_weight * expected_parity_digit f.

Definition payload_of_word (word : nat) : nat :=
  word mod parity_weight.

Definition quotient_after_label (value : nat) : nat :=
  value / label_bound.

Definition quotient_after_sdi (value : nat) : nat :=
  quotient_after_label value / sdi_bound.

Definition quotient_after_data (value : nat) : nat :=
  quotient_after_sdi value / data_bound.

Definition decode_label_from_payload (value : nat) : nat :=
  value mod label_bound.

Definition decode_sdi_from_payload (value : nat) : nat :=
  quotient_after_label value mod sdi_bound.

Definition decode_data_from_payload (value : nat) : nat :=
  quotient_after_sdi value mod data_bound.

Definition decode_ssm_from_payload (value : nat) : nat :=
  quotient_after_data value mod ssm_bound.

Definition decode_fields_from_payload (value : nat) : fields :=
  {|
    label := decode_label_from_payload value;
    sdi := decode_sdi_from_payload value;
    data := decode_data_from_payload value;
    ssm := decode_ssm_from_payload value;
  |}.

Definition decode_label (word : nat) : nat :=
  decode_label_from_payload (payload_of_word word).

Definition decode_sdi (word : nat) : nat :=
  decode_sdi_from_payload (payload_of_word word).

Definition decode_data (word : nat) : nat :=
  decode_data_from_payload (payload_of_word word).

Definition decode_ssm (word : nat) : nat :=
  decode_ssm_from_payload (payload_of_word word).

Definition decode_fields (word : nat) : fields :=
  decode_fields_from_payload (payload_of_word word).

Definition decode_parity_digit (word : nat) : nat :=
  (word / parity_weight) mod 2.

Definition parity_digit_correct (word : nat) : Prop :=
  decode_parity_digit word
    = expected_parity_digit_from_payload (payload_of_word word).

Definition word_valid (word : nat) : Prop :=
  word < word_bound /\ parity_digit_correct word.

Definition word_has_odd_population (word : nat) : Prop :=
  odd_population word_width word = true.

Definition word32_valid (word : word32) : Prop :=
  parity_digit_correct (nat_of_word32 word).

Definition word_well_formed (word : nat) : Prop :=
  exists f, fields_valid f /\ word = encode f.

Definition word32_well_formed (word : word32) : Prop :=
  word_well_formed (nat_of_word32 word).

Record octal_digits := {
  octal_hundreds : nat;
  octal_tens : nat;
  octal_ones : nat;
}.

Definition octal_digits_valid (digits : octal_digits) : Prop :=
  octal_hundreds digits < 4 /\
  octal_tens digits < 8 /\
  octal_ones digits < 8.

Definition label_to_octal (value : nat) : octal_digits :=
  {|
    octal_hundreds := value / 64;
    octal_tens := (value / 8) mod 8;
    octal_ones := value mod 8;
  |}.

Definition octal_to_label (digits : octal_digits) : nat :=
  octal_ones digits
    + 8 * (octal_tens digits + 8 * octal_hundreds digits).

Definition label_partition_index (value : nat) : nat :=
  value / 64.

Definition in_label_partition (index value : nat) : Prop :=
  index < 4 /\ 64 * index <= value < 64 * S index.

Lemma pow2_positive :
  forall n, 0 < pow2 n.
Proof.
  induction n as [|n IH]; simpl; lia.
Qed.

Lemma label_bound_positive :
  0 < label_bound.
Proof.
  exact (pow2_positive label_width).
Qed.

Lemma sdi_bound_positive :
  0 < sdi_bound.
Proof.
  exact (pow2_positive sdi_width).
Qed.

Lemma data_bound_positive :
  0 < data_bound.
Proof.
  exact (pow2_positive data_width).
Qed.

Lemma ssm_bound_positive :
  0 < ssm_bound.
Proof.
  exact (pow2_positive ssm_width).
Qed.

Lemma parity_weight_positive :
  0 < parity_weight.
Proof.
  exact (pow2_positive payload_width).
Qed.

Lemma label_bound_value :
  label_bound = 256.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma sdi_bound_value :
  sdi_bound = 4.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma ssm_bound_value :
  ssm_bound = 4.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma pow2_add :
  forall a b,
    pow2 (a + b) = pow2 a * pow2 b.
Proof.
  induction a as [|a IHa]; intro b.
  - simpl. nia.
  - simpl. rewrite IHa. nia.
Qed.

Lemma parity_weight_factorized :
  parity_weight = label_bound * (sdi_bound * (data_bound * ssm_bound)).
Proof.
  unfold parity_weight, label_bound, sdi_bound, data_bound, ssm_bound,
    payload_width, label_width, sdi_width, data_width, ssm_width.
  replace (pow2 31) with (pow2 (8 + (2 + (19 + 2)))) by reflexivity.
  rewrite (pow2_add 8 (2 + (19 + 2))).
  rewrite (pow2_add 2 (19 + 2)).
  rewrite (pow2_add 19 2).
  reflexivity.
Qed.

Lemma bit_layout_boundaries :
  label_offset = 0 /\
  label_offset + label_width = sdi_offset /\
  sdi_offset + sdi_width = data_offset /\
  data_offset + data_width = ssm_offset /\
  ssm_offset + ssm_width = parity_offset /\
  parity_offset + parity_width = word_width.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

Lemma wire_bit_index_reverses_label_prefix :
  forall position,
    position < label_width ->
    wire_bit_index position = label_width - 1 - position.
Proof.
  intros position Hposition.
  unfold wire_bit_index.
  destruct (position <? label_width) eqn:Hltb.
  - reflexivity.
  - apply Nat.ltb_ge in Hltb.
    lia.
Qed.

Lemma wire_bit_index_is_identity_after_label :
  forall position,
    label_width <= position ->
    wire_bit_index position = position.
Proof.
  intros position Hposition.
  unfold wire_bit_index.
  destruct (position <? label_width) eqn:Hltb.
  - apply Nat.ltb_lt in Hltb.
    lia.
  - reflexivity.
Qed.

Lemma wire_bit_index_range :
  forall position,
    position < word_width ->
    wire_bit_index position < word_width.
Proof.
  intros position Hposition.
  destruct (Nat.lt_ge_cases position label_width) as [Hlabel|Hafter].
  - rewrite wire_bit_index_reverses_label_prefix by exact Hlabel.
    unfold label_width, word_width.
    lia.
  - rewrite wire_bit_index_is_identity_after_label by exact Hafter.
    exact Hposition.
Qed.

Lemma wire_bit_index_label_prefix_involution :
  forall position,
    position < label_width ->
    wire_bit_index (wire_bit_index position) = position.
Proof.
  intros position Hposition.
  replace (wire_bit_index position) with (label_width - 1 - position).
  2:{
    symmetry.
    apply wire_bit_index_reverses_label_prefix.
    exact Hposition.
  }
  assert (Hinner : label_width - 1 - position < label_width) by lia.
  rewrite wire_bit_index_reverses_label_prefix by exact Hinner.
  lia.
Qed.

Lemma mod_digit :
  forall base digit rest,
    0 < base ->
    digit < base ->
    (digit + base * rest) mod base = digit.
Proof.
  intros base digit rest Hbase Hdigit.
  rewrite Nat.mul_comm.
  rewrite Nat.mod_add by lia.
  apply Nat.mod_small.
  exact Hdigit.
Qed.

Lemma extract_bits_range :
  forall value offset width,
    extract_bits value offset width < pow2 width.
Proof.
  intros value offset width.
  unfold extract_bits.
  assert (0 < pow2 width) as Hpow2_pos.
  {
    induction width as [|width IH]; simpl; lia.
  }
  apply Nat.mod_upper_bound.
  lia.
Qed.

Lemma div_digit :
  forall base digit rest,
    0 < base ->
    digit < base ->
    (digit + base * rest) / base = rest.
Proof.
  intros base digit rest Hbase Hdigit.
  rewrite Nat.mul_comm.
  rewrite Nat.div_add by lia.
  rewrite Nat.div_small by lia.
  lia.
Qed.

Lemma extract_bits_insert_bits_zero :
  forall offset width field,
    field < pow2 width ->
    extract_bits (insert_bits 0 offset field) offset width = field.
Proof.
  intros offset width field Hfield.
  unfold extract_bits, insert_bits.
  assert (0 < pow2 offset) as Hoffset_pos.
  {
    induction offset as [|offset IH]; simpl; lia.
  }
  rewrite <- Nat.add_0_l.
  rewrite div_digit with
      (base := pow2 offset)
      (digit := 0)
      (rest := field).
  - apply Nat.mod_small.
    exact Hfield.
  - exact Hoffset_pos.
  - exact Hoffset_pos.
Qed.

Lemma expected_parity_digit_range :
  forall value, expected_parity_digit_from_payload value < 2.
Proof.
  intro value.
  unfold expected_parity_digit_from_payload.
  destruct (odd_population payload_width value); lia.
Qed.

Lemma payload_range :
  forall f, fields_valid f -> payload f < parity_weight.
Proof.
  intros [l s d m] [Hl [Hs [Hd Hm]]].
  unfold payload.
  rewrite parity_weight_factorized.
  pose proof data_bound_positive as Hdata_pos.
  pose proof ssm_bound_positive as Hssm_pos.
  pose proof sdi_bound_positive as Hsdi_pos.
  pose proof label_bound_positive as Hlabel_pos.
  assert (Htail0_step : d + data_bound * m < data_bound * S m).
  {
    replace (data_bound * S m) with (data_bound * m + data_bound) by
      (rewrite Nat.mul_succ_r; lia).
    rewrite (Nat.add_comm (data_bound * m) data_bound).
    apply Nat.add_lt_mono_r.
    exact Hd.
  }
  assert (Htail0_bound : data_bound * S m <= data_bound * ssm_bound).
  {
    assert (HSm : S m <= ssm_bound).
    {
      apply Arith_base.lt_le_S_stt.
      exact Hm.
    }
    exact (Nat.mul_le_mono_l _ _ data_bound HSm).
  }
  assert (Htail0 : d + data_bound * m < data_bound * ssm_bound) by lia.
  assert (Htail1 :
    s + sdi_bound * (d + data_bound * m) <
      sdi_bound * (data_bound * ssm_bound)).
  {
    assert (Htail1_step :
      s + sdi_bound * (d + data_bound * m) <
        sdi_bound * S (d + data_bound * m)).
    {
      replace (sdi_bound * S (d + data_bound * m))
        with (sdi_bound * (d + data_bound * m) + sdi_bound) by
          (rewrite Nat.mul_succ_r; lia).
      rewrite (Nat.add_comm (sdi_bound * (d + data_bound * m)) sdi_bound).
      apply Nat.add_lt_mono_r.
      exact Hs.
    }
    assert (Htail1_bound :
      sdi_bound * S (d + data_bound * m) <=
        sdi_bound * (data_bound * ssm_bound)).
    {
      assert (HSinner : S (d + data_bound * m) <= data_bound * ssm_bound).
      {
        apply Arith_base.lt_le_S_stt.
        exact Htail0.
      }
      exact (Nat.mul_le_mono_l _ _ sdi_bound HSinner).
    }
    lia.
  }
  assert (Houter_step :
    l + label_bound * (s + sdi_bound * (d + data_bound * m)) <
      label_bound * S (s + sdi_bound * (d + data_bound * m))).
  {
    replace (label_bound * S (s + sdi_bound * (d + data_bound * m)))
      with (label_bound * (s + sdi_bound * (d + data_bound * m)) + label_bound) by
        (rewrite Nat.mul_succ_r; lia).
    rewrite (Nat.add_comm (label_bound * (s + sdi_bound * (d + data_bound * m))) label_bound).
    apply Nat.add_lt_mono_r.
    exact Hl.
  }
  assert (Houter_bound :
    label_bound * S (s + sdi_bound * (d + data_bound * m)) <=
      label_bound * (sdi_bound * (data_bound * ssm_bound))).
  {
    assert (HSouter :
      S (s + sdi_bound * (d + data_bound * m)) <=
        sdi_bound * (data_bound * ssm_bound)).
    {
      apply Arith_base.lt_le_S_stt.
      exact Htail1.
    }
    exact (Nat.mul_le_mono_l _ _ label_bound HSouter).
  }
  eapply Nat.lt_le_trans.
  - exact Houter_step.
  - exact Houter_bound.
Qed.

Lemma encode_range :
  forall f, fields_valid f -> encode f < word_bound.
Proof.
  intros f Hvalid.
  unfold encode, word_bound.
  pose proof (payload_range f Hvalid) as Hpayload.
  pose proof (expected_parity_digit_range (payload f)) as Hparity.
  unfold expected_parity_digit in *.
  destruct (expected_parity_digit_from_payload (payload f)) as [|digit] eqn:Hdigit.
  - lia.
  - destruct digit as [|digit].
    + lia.
    + exfalso. lia.
Qed.

Lemma payload_of_word_range :
  forall word, payload_of_word word < parity_weight.
Proof.
  intro word.
  unfold payload_of_word.
  apply Nat.mod_upper_bound.
  intro Hzero.
  pose proof parity_weight_positive as Hpositive.
  rewrite Hzero in Hpositive.
  lia.
Qed.

Lemma decode_fields_from_payload_valid :
  forall value,
    value < parity_weight ->
    fields_valid (decode_fields_from_payload value).
Proof.
  intros value Hvalue.
  unfold fields_valid, decode_fields_from_payload.
  simpl.
  repeat split.
  - unfold decode_label_from_payload.
    apply Nat.mod_upper_bound.
    intro Hzero.
    pose proof label_bound_positive as Hpositive.
    rewrite Hzero in Hpositive.
    lia.
  - unfold decode_sdi_from_payload.
    apply Nat.mod_upper_bound.
    intro Hzero.
    pose proof sdi_bound_positive as Hpositive.
    rewrite Hzero in Hpositive.
    lia.
  - unfold decode_data_from_payload.
    apply Nat.mod_upper_bound.
    intro Hzero.
    pose proof data_bound_positive as Hpositive.
    rewrite Hzero in Hpositive.
    lia.
  - unfold decode_ssm_from_payload.
    apply Nat.mod_upper_bound.
    intro Hzero.
    pose proof ssm_bound_positive as Hpositive.
    rewrite Hzero in Hpositive.
    lia.
Qed.

Lemma decode_fields_valid :
  forall word, fields_valid (decode_fields word).
Proof.
  intro word.
  unfold decode_fields.
  apply decode_fields_from_payload_valid.
  apply payload_of_word_range.
Qed.

Lemma decode_label_from_payload_payload :
  forall f,
    fields_valid f ->
    decode_label_from_payload (payload f) = label f.
Proof.
  intros [l s d m] [Hl [Hs [Hd Hm]]].
  simpl in *.
  unfold decode_label_from_payload, payload.
  change
    ((l + label_bound * (s + sdi_bound * (d + data_bound * m))) mod label_bound = l).
  apply mod_digit.
  - exact label_bound_positive.
  - exact Hl.
Qed.

Lemma decode_sdi_from_payload_payload :
  forall f,
    fields_valid f ->
    decode_sdi_from_payload (payload f) = sdi f.
Proof.
  intros [l s d m] [Hl [Hs [Hd Hm]]].
  simpl in *.
  unfold decode_sdi_from_payload, quotient_after_label, payload.
  change
    (((l + label_bound * (s + sdi_bound * (d + data_bound * m))) / label_bound)
       mod sdi_bound = s).
  rewrite div_digit with
      (base := label_bound)
      (digit := l)
      (rest := s + sdi_bound * (d + data_bound * m)).
  - apply mod_digit.
    + exact sdi_bound_positive.
    + exact Hs.
  - exact label_bound_positive.
  - exact Hl.
Qed.

Lemma decode_data_from_payload_payload :
  forall f,
    fields_valid f ->
    decode_data_from_payload (payload f) = data f.
Proof.
  intros [l s d m] [Hl [Hs [Hd Hm]]].
  simpl in *.
  unfold decode_data_from_payload, quotient_after_sdi, quotient_after_label, payload.
  change
    ((((l + label_bound * (s + sdi_bound * (d + data_bound * m))) / label_bound)
        / sdi_bound) mod data_bound = d).
  rewrite div_digit with
      (base := label_bound)
      (digit := l)
      (rest := s + sdi_bound * (d + data_bound * m)).
  - rewrite div_digit with
        (base := sdi_bound)
        (digit := s)
        (rest := d + data_bound * m).
    + apply mod_digit.
      * exact data_bound_positive.
      * exact Hd.
    + exact sdi_bound_positive.
    + exact Hs.
  - exact label_bound_positive.
  - exact Hl.
Qed.

Lemma decode_ssm_from_payload_payload :
  forall f,
    fields_valid f ->
    decode_ssm_from_payload (payload f) = ssm f.
Proof.
  intros [l s d m] [Hl [Hs [Hd Hm]]].
  simpl in *.
  unfold decode_ssm_from_payload, quotient_after_data, quotient_after_sdi,
    quotient_after_label, payload.
  change
    (((((l + label_bound * (s + sdi_bound * (d + data_bound * m))) / label_bound)
         / sdi_bound) / data_bound) mod ssm_bound = m).
  rewrite div_digit with
      (base := label_bound)
      (digit := l)
      (rest := s + sdi_bound * (d + data_bound * m)).
  - rewrite div_digit with
        (base := sdi_bound)
        (digit := s)
        (rest := d + data_bound * m).
    + rewrite div_digit with
          (base := data_bound)
          (digit := d)
          (rest := m).
      * apply Nat.mod_small.
        exact Hm.
      * exact data_bound_positive.
      * exact Hd.
    + exact sdi_bound_positive.
    + exact Hs.
  - exact label_bound_positive.
  - exact Hl.
Qed.

Lemma decode_fields_from_payload_payload :
  forall f,
    fields_valid f ->
    decode_fields_from_payload (payload f) = f.
Proof.
  intros [l s d m] Hvalid.
  unfold decode_fields_from_payload.
  simpl.
  f_equal.
  - apply decode_label_from_payload_payload.
    exact Hvalid.
  - apply decode_sdi_from_payload_payload.
    exact Hvalid.
  - apply decode_data_from_payload_payload.
    exact Hvalid.
  - apply decode_ssm_from_payload_payload.
    exact Hvalid.
Qed.

Lemma payload_of_word_encode :
  forall f,
    fields_valid f ->
    payload_of_word (encode f) = payload f.
Proof.
  intros f Hvalid.
  unfold payload_of_word, encode.
  apply mod_digit.
  - exact parity_weight_positive.
  - apply payload_range.
    exact Hvalid.
Qed.

Lemma decode_fields_encode :
  forall f,
    fields_valid f ->
    decode_fields (encode f) = f.
Proof.
  intros f Hvalid.
  unfold decode_fields.
  rewrite payload_of_word_encode by exact Hvalid.
  apply decode_fields_from_payload_payload.
  exact Hvalid.
Qed.

Lemma decode_parity_digit_encode :
  forall f,
    fields_valid f ->
    decode_parity_digit (encode f) = expected_parity_digit f.
Proof.
  intros f Hvalid.
  unfold decode_parity_digit, encode.
  rewrite div_digit with
      (base := parity_weight)
      (digit := payload f)
      (rest := expected_parity_digit f).
  - apply Nat.mod_small.
    apply expected_parity_digit_range.
  - exact parity_weight_positive.
  - apply payload_range.
    exact Hvalid.
Qed.

Lemma word_valid_encode :
  forall f,
    fields_valid f ->
    word_valid (encode f).
Proof.
  intros f Hvalid.
  split.
  - apply encode_range.
    exact Hvalid.
  - unfold parity_digit_correct.
    rewrite decode_parity_digit_encode by exact Hvalid.
    rewrite payload_of_word_encode by exact Hvalid.
    reflexivity.
Qed.

Lemma quotient_after_data_range :
  forall value,
    value < parity_weight ->
    quotient_after_data value < ssm_bound.
Proof.
  intros value Hvalue.
  unfold quotient_after_data, quotient_after_sdi, quotient_after_label.
  pose proof label_bound_positive as Hlabel.
  pose proof sdi_bound_positive as Hsdi.
  pose proof data_bound_positive as Hdata.
  rewrite Nat.div_div by lia.
  rewrite Nat.div_div by lia.
  rewrite parity_weight_factorized in Hvalue.
  apply Nat.div_lt_upper_bound; nia.
Qed.

Lemma payload_reconstruction :
  forall value,
    value < parity_weight ->
    payload (decode_fields_from_payload value) = value.
Proof.
  intros value Hvalue.
  set (q0 := value / label_bound).
  set (q1 := q0 / sdi_bound).
  set (q2 := q1 / data_bound).
  assert (Hq0 : value = value mod label_bound + label_bound * q0).
  {
    subst q0.
    pose proof label_bound_positive as Hlabel.
    rewrite Nat.add_comm.
    apply Nat.div_mod.
    lia.
  }
  assert (Hq1 : q0 = q0 mod sdi_bound + sdi_bound * q1).
  {
    subst q1.
    pose proof sdi_bound_positive as Hsdi.
    rewrite Nat.add_comm.
    apply Nat.div_mod.
    lia.
  }
  assert (Hq2 : q1 = q1 mod data_bound + data_bound * q2).
  {
    subst q2.
    pose proof data_bound_positive as Hdata.
    rewrite Nat.add_comm.
    apply Nat.div_mod.
    lia.
  }
  assert (Hq2_small : q2 mod ssm_bound = q2).
  {
    apply Nat.mod_small.
    subst q2 q1 q0.
    apply quotient_after_data_range.
    exact Hvalue.
  }
  unfold payload, decode_fields_from_payload, decode_label_from_payload,
    decode_sdi_from_payload, decode_data_from_payload, decode_ssm_from_payload,
    quotient_after_label, quotient_after_sdi, quotient_after_data.
  cbn [label sdi data ssm].
  fold q0 q1 q2.
  change
    (value mod label_bound
       + label_bound
           * (q0 mod sdi_bound
              + sdi_bound * (q1 mod data_bound + data_bound * (q2 mod ssm_bound)))
     = value).
  rewrite Hq2_small.
  rewrite <- Hq2.
  rewrite <- Hq1.
  rewrite <- Hq0.
  reflexivity.
Qed.

Lemma extract_label_slice_payload :
  forall f,
    fields_valid f ->
    extract_bits (payload f) label_offset label_width = label f.
Proof.
  intros f Hvalid.
  unfold extract_bits, label_offset, label_width.
  change ((payload f / 1) mod label_bound = label f).
  rewrite Nat.div_1_r.
  apply decode_label_from_payload_payload.
  exact Hvalid.
Qed.

Lemma extract_sdi_slice_payload :
  forall f,
    fields_valid f ->
    extract_bits (payload f) sdi_offset sdi_width = sdi f.
Proof.
  intros f Hvalid.
  unfold extract_bits, sdi_offset, sdi_width.
  change (((payload f) / label_bound) mod sdi_bound = sdi f).
  apply decode_sdi_from_payload_payload.
  exact Hvalid.
Qed.

Lemma extract_data_slice_payload :
  forall f,
    fields_valid f ->
    extract_bits (payload f) data_offset data_width = data f.
Proof.
  intros f Hvalid.
  unfold extract_bits, data_offset, data_width.
  replace (pow2 10) with (label_bound * sdi_bound).
  2:{
    unfold label_bound, sdi_bound, label_width, sdi_width.
    replace 10 with (8 + 2) by reflexivity.
    rewrite pow2_add.
    reflexivity.
  }
  rewrite <- Nat.div_div by
    (pose proof label_bound_positive; pose proof sdi_bound_positive; lia).
  change ((((payload f) / label_bound) / sdi_bound) mod data_bound = data f).
  apply decode_data_from_payload_payload.
  exact Hvalid.
Qed.

Lemma extract_ssm_slice_payload :
  forall f,
    fields_valid f ->
    extract_bits (payload f) ssm_offset ssm_width = ssm f.
Proof.
  intros f Hvalid.
  unfold extract_bits, ssm_offset, ssm_width.
  replace (pow2 29) with ((label_bound * sdi_bound) * data_bound).
  2:{
    unfold label_bound, sdi_bound, data_bound,
      label_width, sdi_width, data_width.
    replace 29 with (8 + (2 + 19)) by reflexivity.
    rewrite (pow2_add 8 (2 + 19)).
    rewrite (pow2_add 2 19).
    nia.
  }
  rewrite <- Nat.div_div by
    (pose proof label_bound_positive;
     pose proof sdi_bound_positive;
     pose proof data_bound_positive; lia).
  rewrite <- Nat.div_div by
    (pose proof label_bound_positive; pose proof sdi_bound_positive; lia).
  change (((((payload f) / label_bound) / sdi_bound) / data_bound) mod ssm_bound = ssm f).
  apply decode_ssm_from_payload_payload.
  exact Hvalid.
Qed.

Lemma encode_decode_fields :
  forall word,
    word_valid word ->
    encode (decode_fields word) = word.
Proof.
  intros word [Hrange Hparity].
  unfold parity_digit_correct in Hparity.
  unfold encode, decode_fields, expected_parity_digit.
  rewrite payload_reconstruction by apply payload_of_word_range.
  rewrite <- Hparity.
  unfold decode_parity_digit, payload_of_word.
  pose proof parity_weight_positive as Hpositive.
  assert (Hnz : parity_weight <> 0) by lia.
  assert (Hquot : word / parity_weight < 2).
  {
    apply Nat.div_lt_upper_bound.
    - exact Hnz.
    - replace (parity_weight * 2) with word_bound.
      exact Hrange.
      unfold word_bound.
      rewrite Nat.mul_comm.
      reflexivity.
  }
  rewrite (Nat.mod_small (word / parity_weight) 2) by exact Hquot.
  rewrite Nat.add_comm.
  symmetry.
  apply Nat.div_mod.
  exact Hnz.
Qed.

Lemma bitcount_low_append_digit :
  forall width low digit,
    low < pow2 width ->
    digit < 2 ->
    bitcount_low (S width) (low + digit * pow2 width) =
      bitcount_low width low + digit.
Proof.
  induction width as [|width IH]; intros low digit Hlow Hdigit.
  - simpl in Hlow.
    assert (low = 0) by lia.
    subst low.
    destruct digit as [|[|digit]]; simpl in *; lia.
  - simpl in Hlow.
    change
      (((low + digit * pow2 (S width)) mod 2)
         + bitcount_low (S width) ((low + digit * pow2 (S width)) / 2)
       = low mod 2 + bitcount_low width (low / 2) + digit).
    simpl pow2.
    replace (pow2 width + (pow2 width + 0)) with (2 * pow2 width) by lia.
    replace (digit * (2 * pow2 width)) with ((digit * pow2 width) * 2) by lia.
    rewrite Nat.mod_add by lia.
    replace
      ((low + (digit * pow2 width) * 2) / 2)
      with (low / 2 + digit * pow2 width).
    2: {
      replace (low + (digit * pow2 width) * 2)
        with (((digit * pow2 width) * 2) + low) by lia.
      rewrite Nat.div_add_l by lia.
      lia.
    }
    rewrite IH.
    + lia.
    + apply Nat.div_lt_upper_bound; lia.
    + exact Hdigit.
Qed.

Lemma odd_bitcount_plus_expected_parity :
  forall count,
    Nat.odd
      (count + if Nat.odd count then 0 else 1) = true.
Proof.
  intro count.
  destruct (Nat.odd count) eqn:Hodd.
  - rewrite Nat.add_0_r.
    exact Hodd.
  - rewrite Nat.add_1_r.
    rewrite Nat.odd_succ.
    rewrite <- Nat.negb_odd.
    rewrite Hodd.
    reflexivity.
Qed.

Lemma label_to_octal_valid :
  forall value,
    value < label_bound ->
    octal_digits_valid (label_to_octal value).
Proof.
  intros value Hvalue.
  unfold octal_digits_valid, label_to_octal.
  simpl.
  repeat split.
  - change (value / 64 < 4).
    rewrite label_bound_value in Hvalue.
    apply Nat.div_lt_upper_bound; lia.
  - change ((value / 8) mod 8 < 8).
    apply Nat.mod_upper_bound.
    lia.
  - change (value mod 8 < 8).
    apply Nat.mod_upper_bound.
    lia.
Qed.

Lemma octal_to_label_range :
  forall digits,
    octal_digits_valid digits ->
    octal_to_label digits < label_bound.
Proof.
  intros [h t o] [Hh [Ht Ho]].
  cbn in Hh, Ht, Ho.
  rewrite label_bound_value.
  unfold octal_to_label.
  simpl.
  change (o + 8 * (t + 8 * h) < 256).
  assert (Hh' : h <= 3) by lia.
  assert (Ht' : t <= 7) by lia.
  assert (Hh8 : 8 * h <= 24).
  {
    replace 24 with (8 * 3) by reflexivity.
    apply Nat.mul_le_mono_l.
    exact Hh'.
  }
  assert (Hht : t + 8 * h <= 31).
  {
    eapply Nat.le_trans.
    - apply Nat.add_le_mono; [exact Ht' | exact Hh8].
    - lia.
  }
  nia.
Qed.

Lemma octal_to_label_label_to_octal :
  forall value,
    value < label_bound ->
    octal_to_label (label_to_octal value) = value.
Proof.
  intros value Hvalue.
  set (q0 := value / 8).
  set (q1 := q0 / 8).
  assert (Hq0 : value = value mod 8 + 8 * q0).
  {
    subst q0.
    rewrite Nat.add_comm.
    apply (Nat.div_mod value 8).
    lia.
  }
  assert (Hq1 : q0 = q0 mod 8 + 8 * q1).
  {
    subst q1.
    rewrite Nat.add_comm.
    apply (Nat.div_mod q0 8).
    lia.
  }
  unfold octal_to_label, label_to_octal.
  cbn [octal_hundreds octal_tens octal_ones].
  replace (value / 64) with q1.
  2:{
    subst q1 q0.
    change 64 with (8 * 8).
    rewrite Nat.div_div by lia.
    reflexivity.
  }
  change (value mod 8 + 8 * (q0 mod 8 + 8 * q1) = value).
  rewrite <- Hq1.
  symmetry.
  exact Hq0.
Qed.

Lemma label_to_octal_octal_to_label :
  forall digits,
    octal_digits_valid digits ->
    label_to_octal (octal_to_label digits) = digits.
Proof.
  intros [h t o] [Hh [Ht Ho]].
  cbn in Hh, Ht, Ho.
  unfold label_to_octal, octal_to_label.
  cbn [octal_hundreds octal_tens octal_ones].
  f_equal.
  - replace ((o + 8 * (t + 8 * h)) / 64)
      with (((o + 8 * (t + 8 * h)) / 8) / 8).
    2:{
      change 64 with (8 * 8).
      symmetry.
      rewrite Nat.div_div by lia.
      reflexivity.
    }
    rewrite div_digit with
        (base := 8)
        (digit := o)
        (rest := t + 8 * h) by lia.
    rewrite div_digit with
        (base := 8)
        (digit := t)
        (rest := h) by lia.
    reflexivity.
  - rewrite div_digit with
        (base := 8)
        (digit := o)
        (rest := t + 8 * h) by lia.
    apply mod_digit; lia.
  - apply mod_digit; lia.
Qed.

Lemma label_partition_exists_unique :
  forall value,
    value < label_bound ->
    exists! index, in_label_partition index value.
Proof.
  intros value Hvalue.
  exists (label_partition_index value).
  split.
  - unfold in_label_partition, label_partition_index.
    split.
    + rewrite label_bound_value in Hvalue.
      apply Nat.div_lt_upper_bound; lia.
    + split.
      * apply Nat.mul_div_le.
        lia.
      * apply Nat.mul_succ_div_gt.
        lia.
  - intros index [Hindex Hinterval].
    unfold label_partition_index.
    destruct Hinterval as [Hlow Hhigh].
    apply Nat.le_antisymm.
    + assert (value / 64 < S index).
      {
        apply Nat.div_lt_upper_bound; lia.
      }
      lia.
    + apply Nat.div_le_lower_bound; lia.
Qed.

Lemma label_partition_matches_octal_hundreds :
  forall value,
    value < label_bound ->
    label_partition_index value = octal_hundreds (label_to_octal value).
Proof.
  intros value Hvalue.
  reflexivity.
Qed.

Lemma decode_label_encode :
  forall f,
    fields_valid f ->
    decode_label (encode f) = label f.
Proof.
  intros f Hvalid.
  unfold decode_label.
  rewrite payload_of_word_encode by exact Hvalid.
  apply (decode_label_from_payload_payload f).
  exact Hvalid.
Qed.

Lemma decode_sdi_encode :
  forall f,
    fields_valid f ->
    decode_sdi (encode f) = sdi f.
Proof.
  intros f Hvalid.
  unfold decode_sdi.
  rewrite payload_of_word_encode by exact Hvalid.
  apply (decode_sdi_from_payload_payload f).
  exact Hvalid.
Qed.

Lemma decode_data_encode :
  forall f,
    fields_valid f ->
    decode_data (encode f) = data f.
Proof.
  intros f Hvalid.
  unfold decode_data.
  rewrite payload_of_word_encode by exact Hvalid.
  apply (decode_data_from_payload_payload f).
  exact Hvalid.
Qed.

Lemma decode_ssm_encode :
  forall f,
    fields_valid f ->
    decode_ssm (encode f) = ssm f.
Proof.
  intros f Hvalid.
  unfold decode_ssm.
  rewrite payload_of_word_encode by exact Hvalid.
  apply (decode_ssm_from_payload_payload f).
  exact Hvalid.
Qed.

Lemma encode_injective_on_valid_fields :
  forall f1 f2,
    fields_valid f1 ->
    fields_valid f2 ->
    encode f1 = encode f2 ->
    f1 = f2.
Proof.
  intros f1 f2 Hvalid1 Hvalid2 Hencode.
  apply (f_equal decode_fields) in Hencode.
  rewrite decode_fields_encode in Hencode by exact Hvalid1.
  rewrite decode_fields_encode in Hencode by exact Hvalid2.
  exact Hencode.
Qed.

Lemma decode_fields_injective_on_valid_words :
  forall word1 word2,
    word_valid word1 ->
    word_valid word2 ->
    decode_fields word1 = decode_fields word2 ->
    word1 = word2.
Proof.
  intros word1 word2 Hvalid1 Hvalid2 Hdecode.
  transitivity (encode (decode_fields word1)).
  - symmetry.
    apply encode_decode_fields.
    exact Hvalid1.
  - rewrite Hdecode.
    apply encode_decode_fields.
    exact Hvalid2.
Qed.

Lemma word_valid_iff_encoded_fields :
  forall word,
    word_valid word <->
    exists f, fields_valid f /\ word = encode f.
Proof.
  intro word.
  split.
  - intro Hvalid.
    exists (decode_fields word).
    split.
    + apply decode_fields_valid.
    + symmetry.
      apply encode_decode_fields.
      exact Hvalid.
  - intros [f [Hvalid Hencode]].
    rewrite Hencode.
    apply word_valid_encode.
    exact Hvalid.
Qed.

Lemma word_valid_iff_well_formed :
  forall word,
    word_valid word <-> word_well_formed word.
Proof.
  intro word.
  unfold word_well_formed.
  apply word_valid_iff_encoded_fields.
Qed.

Lemma word32_valid_iff_well_formed :
  forall word,
    word32_valid word <-> word32_well_formed word.
Proof.
  intro word.
  unfold word32_well_formed.
  split.
  - intro Hvalid.
    apply word_valid_iff_well_formed.
    split.
    + exact (word32_range word).
    + exact Hvalid.
  - intro Hwell_formed.
    apply word_valid_iff_well_formed in Hwell_formed.
    exact (proj2 Hwell_formed).
Qed.

Definition encode_word32
  (f : fields)
  (Hvalid : fields_valid f) : word32 :=
  word32_of_nat (encode f) (encode_range f Hvalid).

Definition decode_fields_word32 (word : word32) : fields :=
  decode_fields (nat_of_word32 word).

Definition decode_parity_digit_word32 (word : word32) : nat :=
  decode_parity_digit (nat_of_word32 word).

Lemma nat_of_word32_of_nat :
  forall word Hword,
    nat_of_word32 (word32_of_nat word Hword) = word.
Proof.
  reflexivity.
Qed.

Lemma word32_valid_iff_word_valid :
  forall word,
    word32_valid word <->
    word_valid (nat_of_word32 word).
Proof.
  intro word.
  unfold word32_valid, word_valid, nat_of_word32.
  split.
  - intro Hparity.
    split.
    + exact (word32_range word).
    + exact Hparity.
  - intros [_ Hparity].
    exact Hparity.
Qed.

Lemma encode_word32_refines_encode :
  forall f Hvalid,
    nat_of_word32 (encode_word32 f Hvalid) = encode f.
Proof.
  intros f Hvalid.
  unfold encode_word32.
  apply nat_of_word32_of_nat.
Qed.

Lemma decode_fields_word32_refines_decode_fields :
  forall word,
    decode_fields_word32 word = decode_fields (nat_of_word32 word).
Proof.
  reflexivity.
Qed.

Lemma decode_fields_encode_word32 :
  forall f Hvalid,
    decode_fields_word32 (encode_word32 f Hvalid) = f.
Proof.
  intros f Hvalid.
  unfold decode_fields_word32.
  rewrite encode_word32_refines_encode.
  apply decode_fields_encode.
  exact Hvalid.
Qed.

Lemma encode_decode_word32_refines_nat :
  forall word,
    word32_valid word ->
    encode (decode_fields_word32 word) = nat_of_word32 word.
Proof.
  intros word Hvalid.
  unfold decode_fields_word32.
  apply encode_decode_fields.
  apply (proj1 (word32_valid_iff_word_valid word)).
  exact Hvalid.
Qed.
