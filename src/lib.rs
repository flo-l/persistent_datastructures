#![allow(unused)]

use std::cmp;
use std::cmp::Ordering;
use std::ptr;

#[derive(Clone, Debug)]
//TODO: Clone impl with respect to GC
pub struct AVLTree<K,T> {
    // TODO: GC pointer here
    root: *const Node<K,T>,
}

impl<K: Ord + Clone, T: Clone + PartialEq> AVLTree<K,T> {
    fn empty() -> AVLTree<K,T> {
        AVLTree { root: 0 as *const Node<K,T> }
    }

    fn new(root: *const Node<K,T>) -> AVLTree<K,T> {
        AVLTree { root: root }
    }

    fn get(&self, key: &K) -> Option<&T> {
        let mut current = self.root;
        while !current.is_null() {
            let node = unsafe { &*current };
            match key.cmp(&node.key) {
                Ordering::Less    => current = node.left,
                Ordering::Greater => current = node.right,
                Ordering::Equal   => return Some(&node.data),
            }
        }
        None
    }

    fn has_key(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    // TODO: maybe in place version taking self, which frees the
    // now unused nodes directly.
    fn insert(&self, key: K, data: T) -> AVLTree<K,T> {
        let mut affected_nodes: Vec<(bool, *const Node<K,T>)> = vec![];
        let mut current = self.root;
        while !current.is_null() {
            let node = unsafe { &*current };
            match key.cmp(&node.key) {
                Ordering::Less    => {
                    affected_nodes.push((true, current));
                    current = node.left;
                },
                Ordering::Greater => {
                    affected_nodes.push((false, current));
                    current = node.right;
                },
                Ordering::Equal   => {
                    // optimization if someone inserts the same data with the same key
                    if node.data == data {
                        return self.clone();
                    } else {
                        break;
                    }
                },
            }
        }

        current = Node::new(ptr::null(), ptr::null(), key, data, 0);
        // check if we change the heigt of the tree.
        let mut height_changed = match affected_nodes.last() {
            Some(&(left, node_ptr)) => {
                let node = unsafe { &*node_ptr };
                (left && node.right.is_null()) || (!left && node.left.is_null())
             }
             None => false,
        };

        height_changed = true;
        for (left, node) in affected_nodes.into_iter().rev() {
            let node = unsafe{ &*node };
            if left {
                let balance = if height_changed {
                    node.balance + 1
                } else {
                    node.balance
                };
                if node.balance < 0 { height_changed = false }
                current = Node::new(current, node.right, node.key.clone(), node.data.clone(), balance);
            } else {
                let balance = if height_changed {
                    node.balance - 1
                } else {
                    node.balance
                };
                if node.balance > 0 { height_changed = false }
                current = Node::new(node.left, current, node.key.clone(), node.data.clone(), balance);
            }
        }

        AVLTree::new(current)
    }
}

impl<'a, K, T> IntoIterator for &'a AVLTree<K,T> where K: 'a, T: 'a {
    type Item = (&'a K, &'a T);
    type IntoIter = AVLTreeIter<'a, K, T>;

    fn into_iter(self) -> Self::IntoIter {
        AVLTreeIter::new(self)
    }
}

#[derive(Debug)]
struct Node<K,T> {
    pub left:  *const Node<K,T>,
    pub right: *const Node<K,T>,
    pub key: K,
    pub data: T,
    pub balance: i8,
}

impl<K,T> Node<K,T> {
    fn new(left: *const Node<K,T>, right: *const Node<K,T>, key: K, data: T, balance: i8) -> *const Node<K,T> {
        let node = Node {
            left:  left,
            right: right,
            key: key,
            data: data,
            balance: balance,
        };

        Box::into_raw(Box::new(node))
    }

    fn compute_heights(&self) -> (usize, usize) {
        let left = if self.left.is_null() {
            0
        } else {
            unsafe { (*self.left).height() + 1}
        };

        let right = if self.right.is_null() {
            0
        } else {
            unsafe { (*self.right).height() + 1}
        };

        (left, right)
    }

    // determine height recursively
    // height is defined as max. of number of nodes of left or right children
    fn height(&self) -> usize {
        let (left, right) = self.compute_heights();
        cmp::max(left, right)
    }
}

#[derive(Debug)]
pub struct AVLTreeIter<'a, K, T> where K: 'a, T: 'a {
    tree: &'a AVLTree<K,T>,
    half_visited: Vec<*const Node<K,T>>,
}

impl<'a, K, T> AVLTreeIter<'a, K, T> {
    fn new(tree: &'a AVLTree<K,T>) -> Self {
        let mut half_visited = vec![tree.root];

        let mut current = tree.root;
        let mut next    = unsafe { (*current).left };
        // go down the tree on the left as far as possible
        while !next.is_null() {
            unsafe {
                current = next;
                next = (*next).left;
            }
            half_visited.push(current)
        }

        AVLTreeIter { tree: tree, half_visited: half_visited }
    }
}

impl<'a, K, T> Iterator for AVLTreeIter<'a, K, T> where K: 'a {
    type Item = (&'a K, &'a T);
    fn next(&mut self) -> Option<Self::Item> {
        let mut current = match self.half_visited.pop() {
            Some(x) => x,
            None    => return None,
        };
        let mut next = unsafe { (*current).right };
        // item to be returned
        let ret = unsafe { (&(*current).key, &(*current).data) };

        // traverse the right tree on the left as far as possible
        while !next.is_null() {
            unsafe {
                current = next;
                next = (*next).left;
            }
            self.half_visited.push(current);
        }

        Some(ret)
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Node, AVLTree
    };

    #[test]
    fn test_insert() {
        let tree: AVLTree<u32, ()> = AVLTree::empty();
        assert!(!tree.has_key(&0));
        assert!(!tree.has_key(&42));

        let tree2 = tree.insert(845, ());
        assert!(!tree.has_key(&845));
        assert!(tree2.has_key(&845));

        let numbers = [9, 34, 764, 234, 0, 12345, 435, 1234, 45];
        let mut tree: AVLTree<u32, ()> = AVLTree::empty();
        for x in 0..numbers.len() {
            tree = tree.insert(numbers[x], ());
            for y in &numbers[0..x] {
                assert!(tree.has_key(y));
            }
        }
    }

    #[test]
    fn test_iterator() {
        let mut numbers = vec![9u32, 34, 764, 234, 0, 12345, 435, 1234, 45];
        let mut tree: AVLTree<u32, ()> = AVLTree::empty();
        for x in &numbers {
            tree = tree.insert(*x, ());
        }

        let sorted: Vec<u32> = tree.into_iter().map(|(&x, _)| x).collect();
        numbers.sort();
        assert_eq!(sorted, numbers);
    }

    #[test]
    fn test_balances() {
        let mut tree: AVLTree<u32, ()> = AVLTree::empty();
        tree = tree.insert(5, ());
        unsafe {
            assert_eq!((*tree.root).balance, 0);
        }

        tree = tree.insert(2, ());
        unsafe {
            assert_eq!((*tree.root).balance, 1);
            assert_eq!((*(*tree.root).left).balance, 0);
        }

        tree = tree.insert(3, ());
        unsafe {
            assert_eq!((*tree.root).balance, 2);
            assert_eq!((*(*tree.root).left).balance, -1);
            assert_eq!((*(*(*tree.root).left).right).balance, 0);
        }

        tree = tree.insert(4, ());
        unsafe {
            assert_eq!((*tree.root).balance, 3);
            assert_eq!((*(*tree.root).left).balance, -2);
            assert_eq!((*(*(*tree.root).left).right).balance, -1);
            assert_eq!((*(*(*(*tree.root).left).right).right).balance, 0);
        }

        tree = tree.insert(1, ());
        unsafe {
            assert_eq!((*tree.root).balance, 3);
            assert_eq!((*(*tree.root).left).balance, -1);
            assert_eq!((*(*(*tree.root).left).right).balance, -1);
            assert_eq!((*(*(*tree.root).left).left).balance, 0);
            assert_eq!((*(*(*(*tree.root).left).right).right).balance, 0);
        }

        tree = tree.insert(6, ());
        unsafe {
            assert_eq!((*tree.root).balance, 2);
            assert_eq!((*(*tree.root).left).balance, -1);
            assert_eq!((*(*tree.root).right).balance, 0);
            assert_eq!((*(*(*tree.root).left).right).balance, -1);
            assert_eq!((*(*(*tree.root).left).left).balance, 0);
            assert_eq!((*(*(*(*tree.root).left).right).right).balance, 0);
        }

        tree = tree.insert(7, ());
        unsafe {
            assert_eq!((*tree.root).balance, 1);
            assert_eq!((*(*tree.root).left).balance, -1);
            assert_eq!((*(*tree.root).right).balance, -1);
            assert_eq!((*(*(*tree.root).left).right).balance, -1);
            assert_eq!((*(*(*tree.root).right).right).balance, 0);
            assert_eq!((*(*(*tree.root).left).left).balance, 0);
            assert_eq!((*(*(*(*tree.root).left).right).right).balance, 0);
        }
    }

/*
    #[test]
    fn test_height() {
        let mut root = Node::new(0);
        let mut l1   = Node::new(1);
        let mut r1   = Node::new(2);
        root.left = &l1;
        root.right = &r1;
        assert_eq!(root.height(), 1);

        let mut r12  = Node::new(3);
        r1.right = &r12;
        assert_eq!(root.height(), 2);
        assert_eq!(r1.height(), 1);
        assert_eq!(l1.height(), 0);

        let l123  = Node::new(4);
        r12.left = &l123;
        assert_eq!(root.height(), 3);
    }
*/
}
