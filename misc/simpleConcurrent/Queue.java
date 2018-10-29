package simpleConcurrent;

import java.util.concurrent.atomic.AtomicReference;

public class Queue <E> {
    AtomicReference<Node<E>> head, tail;

    public Queue() {
        tail = new AtomicReference<Node<E>>(new Node<E>(null));
        head = new AtomicReference<Node<E>>(tail.get());
    }

    public boolean offer(E e) {
        if (e == null) throw new NullPointerException();
        final Node<E> newNode = new Node<E>(e);

        Node<E> myTail, myTailNext;
        while (true) {
            myTail = tail.get();
            myTailNext = myTail.next.get();

            if (myTailNext == null) {
                if (myTail.next.compareAndSet(myTailNext, newNode))
                    return true;
            } else {  // Try to advance tail
                tail.compareAndSet(myTail, myTailNext);
            }
        }
    }

    public E poll() {
        E val;

        while (true) {
            Node<E> myHead = head.get();
            Node<E> myTail = tail.get();
            Node<E> myHeadNext = myHead.next.get();

            if (myHead == myTail) {
                if (myHeadNext == null) {
                    return null;
                }
                tail.compareAndSet(myTail, myHeadNext);  // Try to advance tail
            } else {
                val = myHeadNext.item;
                if (head.compareAndSet(myHead, myHeadNext))
                    return val;
            }  // Else, try again from top
        }
    }

    public int size() {
        int count = 0;
        for (Node<E> p = head.get(); p != null; ) {
            ++count;
            p = p.next.get();
        }
        return count;
    }

    private static class Node <E> {
        public final E item;
        public AtomicReference<Node<E>> next;

        public Node(E item) {
            this.item = item;
            this.next = new AtomicReference<Node<E>>();
        }
    }
}