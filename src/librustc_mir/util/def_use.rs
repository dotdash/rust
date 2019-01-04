//! Def-use analysis.

use rustc::mir::{Local, Location, Mir, Place};
use rustc::mir::visit::{PlaceContext, MutVisitor, Visitor};
use rustc_data_structures::indexed_vec::IndexVec;
use std::marker::PhantomData;
use std::mem;
use std::slice;
use std::iter;

pub struct DefUseAnalysis<'tcx> {
    info: IndexVec<Local, Info<'tcx>>,
}

#[derive(Clone)]
pub struct Info<'tcx> {
    pub defs_and_uses: Vec<Use<'tcx>>,
}

#[derive(Clone, PartialEq)]
pub struct Use<'tcx> {
    pub context: PlaceContext<'tcx>,
    pub location: Location,
}

impl<'tcx> DefUseAnalysis<'tcx> {
    pub fn new(mir: &Mir<'tcx>) -> DefUseAnalysis<'tcx> {
        DefUseAnalysis {
            info: IndexVec::from_elem_n(Info::new(), mir.local_decls.len()),
        }
    }

    pub fn analyze(&mut self, mir: &Mir<'tcx>) {
        self.clear();

        let mut finder = DefUseFinder {
            info: mem::replace(&mut self.info, IndexVec::new()),
        };
        finder.visit_mir(mir);
        self.info = finder.info
    }

    fn clear(&mut self) {
        for info in &mut self.info {
            info.clear();
        }
    }

    pub fn local_info(&self, local: Local) -> &Info<'tcx> {
        &self.info[local]
    }

    fn mutate_defs_and_uses<F>(&mut self, local: Local, mir: &mut Mir<'tcx>, callback: F)
                               where F: for<'a> FnMut(&'a mut Place<'tcx>) + Copy {
        for place_use in &self.info[local].defs_and_uses.clone() {
            MutateUseVisitor::new(local,
                                  callback,
                                  |local, context, location, add| {
                                      if add {
                                          self.info[*local].defs_and_uses.push(Use { context, location });
                                      } else {
                                          self.info[*local].defs_and_uses.remove_item(&Use { context, location });
                                      }
                                  },
                                  mir).visit_location(mir, place_use.location)
        }
    }

    /// FIXME(pcwalton): This should update the def-use chains.
    pub fn replace_all_defs_and_uses_with(&mut self,
                                          local: Local,
                                          mir: &mut Mir<'tcx>,
                                          new_place: Place<'tcx>) {
        let new_place = &new_place;
        self.mutate_defs_and_uses(local, mir, move |place| *place = new_place.clone());
    }
}

struct DefUseFinder<'tcx> {
    info: IndexVec<Local, Info<'tcx>>,
}

impl<'tcx> Visitor<'tcx> for DefUseFinder<'tcx> {
    fn visit_local(&mut self,
                   &local: &Local,
                   context: PlaceContext<'tcx>,
                   location: Location) {
        self.info[local].defs_and_uses.push(Use {
            context,
            location,
        });
    }
}

impl<'tcx> Info<'tcx> {
    fn new() -> Info<'tcx> {
        Info {
            defs_and_uses: vec![],
        }
    }

    fn clear(&mut self) {
        self.defs_and_uses.clear();
    }

    pub fn def_count(&self) -> usize {
        self.defs_and_uses.iter().filter(|place_use| place_use.context.is_mutating_use()).count()
    }

    pub fn def_count_not_including_drop(&self) -> usize {
        self.defs_not_including_drop().count()
    }

    pub fn defs_not_including_drop(
        &self,
    ) -> iter::Filter<slice::Iter<Use<'tcx>>, fn(&&Use<'tcx>) -> bool> {
        self.defs_and_uses.iter().filter(|place_use| {
            place_use.context.is_mutating_use() && !place_use.context.is_drop()
        })
    }

    pub fn use_count(&self) -> usize {
        self.defs_and_uses.iter().filter(|place_use| {
            place_use.context.is_nonmutating_use()
        }).count()
    }
}

struct MutateUseVisitor<'tcx, F, F2> {
    query: Local,
    callback: F,
    callback2: F2,
    add: Option<bool>,
    phantom: PhantomData<&'tcx ()>,
}

impl<'tcx, F, F2> MutateUseVisitor<'tcx, F, F2> {
    fn new(query: Local, callback: F, callback2: F2, _: &Mir<'tcx>)
           -> MutateUseVisitor<'tcx, F, F2>
               where F: for<'a> FnMut(&'a mut Place<'tcx>),
                     F2: for<'a> FnMut(&'a mut Local, PlaceContext<'tcx>, Location, bool) {
        MutateUseVisitor {
            query,
            callback,
            callback2,
            add: None,
            phantom: PhantomData,
        }
    }
}

impl<'tcx, F, F2> MutVisitor<'tcx> for MutateUseVisitor<'tcx, F, F2>
where F: for<'a> FnMut(&'a mut Place<'tcx>),
      F2: for<'a> FnMut(&'a mut Local, PlaceContext<'tcx>, Location, bool) {
    fn visit_place(&mut self,
                   place: &mut Place<'tcx>,
                   context: PlaceContext<'tcx>,
                   location: Location) {
        if self.add.is_none() && context.is_use() && *place == Place::Local(self.query) {
            self.add = Some(false);
            self.super_place(place, context, location);

            (self.callback)(place);

            self.add = Some(true);
            self.super_place(place, context, location);

            self.add = None;
        }

        self.super_place(place, context, location);
    }

    fn visit_local(&mut self,
                    local: &mut Local,
                    context: PlaceContext<'tcx>,
                    location: Location) {
        if let Some(add) = self.add {
            if context.is_use() && *local == self.query {
                (self.callback2)(local, context, location, add)
            }
        }
    }
}
