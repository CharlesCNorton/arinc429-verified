# ARINC 429 Formalization TODO

1. Fix the target standard. Pin one exact ARINC 429 revision and trace every definition, invariant, and theorem back to named clauses.
2. Kill the unbounded-word abstraction. Replace the `nat`-level word with a true 32-bit model and prove the current arithmetic packing is a refinement, not the foundation.
3. Make bits first-class. Define extraction, insertion, masking, and field slicing explicitly, then prove every field occupies exactly its mandated bit positions.
4. Upgrade well-formedness. Redefine `word_valid` as full structural validity of an ARINC word, not merely numeric range plus stored-parity agreement.
5. Close the parity hole. Prove that every encoded valid word has true odd population across all 32 bits.
6. Fix label semantics at the wire. Formalize octal-label meaning, label bit order, and transmission-order reversal, then prove the wire label matches the abstract label exactly.
7. Build the real serializer. Define the exact word-to-wire bit stream, including ordering and parity placement, and prove it is standard-conformant.
8. Build the real deserializer. Define wire-to-word reconstruction and prove it inverts the serializer under valid transmission assumptions.
9. Formalize the signal itself. Model bipolar RZ levels, null state, and receiver interpretation thresholds.
10. Formalize time, not just bits. Model both ARINC data rates, tolerance bounds, bit timing, and interword gaps.
11. Prove the machines. Define transmitter and receiver state machines and prove they emit and accept only standard-conformant behavior.
12. Admit the world is hostile. Add a channel and fault model for noise, jitter, flips, truncation, and timing distortion.
13. Make failure semantics explicit. Define exactly which malformed or faulted inputs are rejected, and classify the rejection reasons.
14. Stop treating SDI as raw bits. Give SDI actual routing semantics.
15. Stop treating SSM as raw bits. Give SSM typed status semantics.
16. Stop treating payload as an anonymous integer. Define typed payload models for BNR, BCD, discrete, maintenance, and other ARINC-relevant encodings.
17. Build a label dictionary. Assign each supported label a payload type and legal SDI/SSM interpretation.
18. Enforce label-specific legality. Formalize reserved labels, forbidden encodings, and installation-specific constraints where applicable.
19. Lift correctness to typed messages. Prove encode/decode roundtrip for real message types, not just raw field tuples.
20. Lift uniqueness to typed messages. Prove non-aliasing and uniqueness at the typed-message level across the supported label space.
21. Cross-check reality. Validate the formal model against at least one independent encoder/decoder and a conformance corpus of valid and malformed vectors.
22. Generate something executable. Derive a reference implementation from the formal model and prove it equivalent to the spec.
23. Close the implementation gap. Prove equivalence between the formal model and target HDL, firmware, or host-side software artifacts.
24. Split the monolith. Refactor the development into auditable modules for word format, wire semantics, timing, faults, typing, and conformance.
25. Remove proof-ecosystem rot. Eliminate deprecated Rocq/Coq dependencies and stabilize the proof base on current lemmas only.
26. Finish the certification story. Add assumptions, guarantees, traceability tables, proof obligations, theorem indexing, and review artifacts fit for external audit.
