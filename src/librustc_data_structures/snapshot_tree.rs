use snapshot_vec::*;
use core::slice::{Iter, IterMut};
// use std::marker::{Deref, DerefMut};

#[allow(dead_code)]

pub struct SnapshotTree<T> {
    vec: SnapshotVec<Node<T>>
}

pub struct Node<T> {
    pub elem: T,
    // Roots don't have a parent
    parent: Option<u32>,
    child: Option<u32>,
    sibling: Option<u32>
}

pub struct UndoNode<T> {
    node: u32,
    value: Option<T>,
    child: Option<u32>,
    sibling: Option<u32>
}

impl<T> SnapshotVecDelegate for Node<T> {
    type Value = Node<T>;
    type Undo  = UndoNode<T>;

    fn reverse(values: &mut Vec<Self::Value>, action: Self::Undo) {
        ()
        //let node = &mut values[action.node as usize];
        // node.elem = action.value.unwrap_or(node.elem);
        // node.child = action.child.unwrap_or(node.child);
        // node.sibling = action.sibling.unwrap_or(node.sibling);
    }
}

impl<T> SnapshotTree<T> {
    pub fn new() -> SnapshotTree<T> {
        SnapshotTree { vec: SnapshotVec::new() }
    }

    pub fn insert_root(&mut self, elem: T) -> u32 {
        // No root
        if self.vec.len() == 0 {
            self.new_node(elem, None)
        } else {
            // this is the case where we want to treat it like a forest
            let id = self.new_node(elem, Some(0));
            self.append_child(0, id); id
        }
    }

    pub fn insert_child(&mut self, parent: u32, elem: T) -> u32 {
        panic!()
    }

    pub fn len(&self) -> usize {
        self.vec.len()
    }

    pub fn nodes(&self) -> Iter<Node<T>> {
        self.vec.iter()
    }

    pub fn nodes_mut(&mut self) -> IterMut<Node<T>> {
        self.vec.iter_mut()
    }

    // Allocates a new node with specified elem and parent. Returns the id of the new Node and
    pub fn new_node(&mut self, elem: T, parent: Option<u32>) -> u32 {
        let next_node_index = self.vec.len();
        let node = Node {
            elem: elem,
            parent: parent,
            child: None,
            sibling: None,
        };
        self.vec.push(node);
        next_node_index as u32
    }

    fn append_child(&mut self, node: u32, new_child: u32) {
        let mut node = node;
        let mut child = self.vec[node as usize].child;

        while let Some(next_node) = child {
           node = next_node;
           child = self.vec[node as usize].child;
        }

        assert!(self.vec[node as usize].child == None);

        self.vec[node as usize].child = Some(new_child);
    }
}

