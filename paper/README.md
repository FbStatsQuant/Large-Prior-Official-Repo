# Lemma proofs

[`lemma_proofs.pdf`](lemma_proofs.pdf) has the full proofs of the lemmas stated in the paper's Appendix. They didn't fit within the page limit of the submitted version, so they live here.

- Lemmas 1–4 build up to Theorem 1: local prior mass, the evidence bound, the sieve and the tests. The tests lemma also needs three supporting lemmas (S1–S3): a basic Gaussian test, a packing bound and a covering of the shells.
- Lemmas 5–8 build up to Corollary 1: exponent algebra, the size of the budget, the sparse approximant, and the variance and rate.
- Lemmas 9–10 are the sparse approximation results for the multiresolution B-spline and Fourier dictionaries.

Numbers without a prefix refer to the paper. Lemmas and equations numbered S1, S2, … are introduced in the companion.

Theorem 1 and Corollary 1 are also checked end to end in Lean 4; see [`../lean`](../lean).
