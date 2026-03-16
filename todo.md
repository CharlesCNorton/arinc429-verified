# ARINC 429 Formalization TODO

1. Fix the target standard by formalizing one exact ARINC 429 revision and build a clause-by-clause trace matrix from that document into the Coq development.
2. Introduce a true 32-bit word model and prove it equivalent to the current arithmetic packing model.
3. Formalize bit extraction, bit insertion, and field masking, and prove that every field occupies exactly its mandated bit positions.
4. Formalize the ARINC 429 label bit-order and transmission-order semantics and prove the octal label model matches the wire-level label exactly.
5. Formalize the complete word-to-wire serializer, including bit sequence, ordering, and parity placement.
6. Formalize the wire-to-word deserializer and prove it is the inverse of the serializer under valid transmission assumptions.
7. Formalize the electrical signaling layer, including bipolar RZ levels, null state, and receiver interpretation thresholds.
8. Formalize the timing layer, including both data rates, tolerance bounds, bit timing, and interword gap requirements.
9. Formalize the transmitter state machine and prove it emits only standard-conformant waveforms and timing.
10. Formalize the receiver state machine and prove it reconstructs words correctly from conformant waveforms.
11. Formalize a channel and fault model covering noise, jitter, bit flips, truncation, and timing distortion.
12. Strengthen `word_valid` from numeric range plus parity consistency into full standards-level word well-formedness.
13. Prove that every encoded valid word has true odd population at the 32-bit level, not merely a correct stored parity digit.
14. Define explicit acceptance and rejection semantics for malformed or faulted received words, with named error classes.
15. Formalize SDI semantics as actual message-routing semantics rather than a raw 2-bit field.
16. Formalize SSM semantics as typed status semantics rather than a raw 2-bit field.
17. Formalize typed payload semantics for BNR, BCD, discrete, maintenance, and other ARINC-relevant encodings.
18. Build a label dictionary that assigns each supported label a typed payload schema and legal SDI/SSM interpretation.
19. Formalize label-specific legality rules, including reserved labels, forbidden encodings, and installation-specific constraints where applicable.
20. Prove encode/decode correctness for typed messages, not just raw field tuples.
21. Prove uniqueness and non-aliasing at the typed message level across the supported label space.
22. Prove interoperability by validating the formal spec against at least one independently implemented encoder and decoder.
23. Derive an executable reference implementation from the formal model and prove it equivalent to the specification.
24. Prove equivalence between the formal model and target implementation artifacts such as HDL, firmware, or host-side libraries.
25. Refactor the development into audited modules for word format, wire semantics, timing, faults, typing, and conformance.
26. Add certification-grade artifacts: assumptions, guarantees, proof obligations, traceability tables, and reviewable theorem indexing.
27. Add a conformance corpus of canonical vectors, malformed vectors, and fault-injection cases and prove the implementation matches them.
28. Eliminate deprecated proof dependencies and bring the proof base onto stable, current library lemmas only.
