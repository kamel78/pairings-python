# Bilinearity-Pairings Library with Python (from scratch)

This library implements the necessary materials and mechanisms for bilinearity-pairings-based cryptography from scratch using Python. While Python may not be the most favorable environment for achieving the best timing results, we have chosen it for its simplicity and flexibility to serve as a reference implementation for pairing-based constructions.

## Implemented Curves

The implemented curves are those selected and standardized in the draft-irtf-cfrg-pairing-friendly-curves, specifically:

- BLS12 curve for the 128-bit security level
- BLS24 curve for the 192-bit security level
- BLS48 curve for the 256-bit security level

### Included Parameters

- 381-bit and 461-bit for BLS12
- 479-bit and 559-bit for BLS24
- 575-bit for BLS48

For a comprehensive set of the used parameters, please consult the file `filename`.

## BLS48 Implementation

It's worth noting that the BLS48 implementation differs from the one selected in the draft. We propose an alternative construction and parameters that are more efficient and secure. Our proposed curve addresses issues with the curve initially suggested by Y. Kiyomura, which unfortunately lacks isogenies of prime order, making hashing to G2 impossible to implement in a constant-time manner. Additionally, our proposed curve has more efficient arithmetic.

## Optimizations and Constant-Time Implementations

Furthermore, the library includes several (personal) optimizations and constant-time implementations of various operations, such as hashing to G1-G2, optimal recording of scalars, and isogeny construction. Some of the implemented tricks are new personal contributions that are currently under consideration for publication. Notably, these optimizations focus on the hashing of the curve and scalar multiplication operations.

We welcome all comments and remarks.
