package ss.week4;

public class DoublyLinkedList<E> {

    private /*@ spec_public @*/ int size;
    private Node head;

    //@ ensures this.size == 0;
    public DoublyLinkedList() {
        size = 0;
        head = new Node(null);
        head.next = head;
        head.previous = head;
    }

    //@ requires element != null;
    //@ requires 0 <= index && index <= this.size;
    //@ ensures this.size == \old(size) + 1;
    //@ ensures this.getNode(index).equals(element);
    public void add(int index, E element) {
    	Node addnode = new Node(element);
    	Node prevnode = getNode(index);
    	addnode.previous = prevnode.previous;
    	addnode.next = prevnode;
    	prevnode.previous.next = addnode;
    	prevnode.previous = addnode;
    	size = size + 1;
    }

    //@ requires 0 <= index && index < this.size;
    //@ ensures this.size == \old(size) - 1;
    public void remove(int index) {
        Node removenode = getNode(index);
        removenode.previous.next = removenode.next;
        removenode.next.previous = removenode.previous;
        size = size - 1;
    }

    //@ requires 0 <= index && index < this.size;
    /*@ pure */ public E get(int index) {
        Node p = getNode(index);
        return p.element;
    }

    /**
     * The node containing the element with the specified index.
     * The head node if the specified index is -1.
     */
    //@ requires -1 <= i && i < this.size;
    //@ pure
    public Node getNode(int i) {
        Node p = head;
        int pos = -1;
        while (pos < i) {
            p = p.next;
            pos = pos + 1;
        }
        return p;
    }

    public int size() {
        return this.size;
    }
    public class Node {
        public Node(E element) {
            this.element = element;
            this.next = null;
            this.previous = null;
        }

        private E element;
        public Node next;
        public Node previous;

        public E getElement() {
            return element;
        }
    }
}
