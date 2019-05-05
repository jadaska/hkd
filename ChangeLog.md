# Changelog for hkd

# 0.1.0

# 0.2.0
- Refactored all the generic hoist, traverse, fold, zip
  functionality into a typeclasses HKDHoist, HKDSequence,
  HKDFold, HKDDefault, HKDZip.
- Added an HKDF t a f to hold t (a f) stuctures. This
  allows definition of data types with containers (e.g., [a f])
  to take the form an HKD form (e.g., [a f] ~ a' f where a' = HKDF [] a)
- Rename a number of functions to gn* to hkd* (e.g., hkdhoist)

## Unreleased changes
