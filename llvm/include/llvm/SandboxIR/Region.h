//===- Region.h -------------------------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_VECTORIZE_SANDBOXVECTORIZER_REGION_H
#define LLVM_TRANSFORMS_VECTORIZE_SANDBOXVECTORIZER_REGION_H

#include <memory>

#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/SandboxIR/Instruction.h"
#include "llvm/Support/raw_ostream.h"

namespace llvm::sandboxir {

/// The main job of the Region is to point to new instructions generated by
/// vectorization passes. It is the unit that RegionPasses operate on with their
/// runOnRegion() function.
///
/// The region allows us to stack transformations horizontally, meaning that
/// each transformation operates on a single region and the resulting region is
/// the input to the next transformation, as opposed to vertically, which is the
/// common way of applying a transformation across the whole function. This
/// enables us to check for profitability and decide whether we accept or
/// rollback at a region granularity, which is much better than doing this at
/// the function level.
///
//  Traditional approach: transformations applied vertically for the whole
//  function
//    F
//  +----+
//  |    |
//  |    |
//  |    | -> Transform1 ->  ... -> TransformN -> Check Cost
//  |    |
//  |    |
//  +----+
//
//  Region-based approach: transformations applied horizontally, for each Region
//    F
//  +----+
//  |Rgn1| -> Transform1 ->  ... -> TransformN -> Check Cost
//  |    |
//  |Rgn2| -> Transform1 ->  ... -> TransformN -> Check Cost
//  |    |
//  |Rgn3| -> Transform1 ->  ... -> TransformN -> Check Cost
//  +----+

class Region {
  /// All the instructions in the Region. Only new instructions generated during
  /// vectorization are part of the Region.
  SetVector<Instruction *> Insts;

  /// MDNode that we'll use to mark instructions as being part of the region.
  MDNode *RegionMDN;
  static constexpr const char *MDKind = "sandboxvec";
  static constexpr const char *RegionStr = "sandboxregion";

  Context &Ctx;

  /// ID (for later deregistration) of the "create instruction" callback.
  Context::CallbackID CreateInstCB;
  /// ID (for later deregistration) of the "erase instruction" callback.
  Context::CallbackID EraseInstCB;

  // TODO: Add cost modeling.
  // TODO: Add a way to encode/decode region info to/from metadata.

public:
  Region(Context &Ctx);
  ~Region();

  Context &getContext() const { return Ctx; }

  /// Adds I to the set.
  void add(Instruction *I);
  /// Removes I from the set.
  void remove(Instruction *I);
  /// Returns true if I is in the Region.
  bool contains(Instruction *I) const { return Insts.contains(I); }
  /// Returns true if the Region has no instructions.
  bool empty() const { return Insts.empty(); }

  using iterator = decltype(Insts.begin());
  iterator begin() { return Insts.begin(); }
  iterator end() { return Insts.end(); }
  iterator_range<iterator> insts() { return make_range(begin(), end()); }

  static SmallVector<std::unique_ptr<Region>> createRegionsFromMD(Function &F);

#ifndef NDEBUG
  /// This is an expensive check, meant for testing.
  bool operator==(const Region &Other) const;
  bool operator!=(const Region &other) const { return !(*this == other); }

  void dump(raw_ostream &OS) const;
  void dump() const;
  friend raw_ostream &operator<<(raw_ostream &OS, const Region &Rgn) {
    Rgn.dump(OS);
    return OS;
  }
#endif
};

} // namespace llvm::sandboxir

#endif // LLVM_TRANSFORMS_VECTORIZE_SANDBOXVECTORIZER_REGION_H
