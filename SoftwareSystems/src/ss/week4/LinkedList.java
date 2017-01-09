package ss.week4;

public class LinkedList<E> {

	private /* @ spec_public @ */ int size;
	private Node first;

	// @ ensures \result.size == 0;
	public LinkedList() {
		size = 0;
		first = null;
	}

	public void add(int index, E element) {
		Node newNode = new Node(element);
		if (index == 0) {
			newNode.next = first;
			first = newNode;
		} else {
			Node p = getNode(index - 1);
			newNode.next = p.next;
			p.next = newNode;
		}
		size = size + 1;
	}

	// @ ensures this.size == \old(size) - 1;
	public void remove(E element) {
		Node search = findBefore(element);
		if (search != null) {
			search.next = search.next.next;
			size = size - 1;
		} else if (first.element == element) {
			first = first.next;
			size = size - 1;
		}
	}

	public Node findBefore(E element) {
		Node tester = first;
		for (int i = 0; i < size; i++) {
			if (tester != first && tester.element == element) {
				return getNode(i - 1);
			}
			if (i < size - 1) {
				tester = tester.next;
			}
		}
		return null;
	}

	// @ requires 0 <= index && index < this.size();
	public E get(int index) {
		Node p = getNode(index);
		return p.element;
	}

	// @ requires 0 <= i && i < this.size();
	private /* @ pure @ */ Node getNode(int i) {
		Node p = first;
		int pos = 0;
		while (pos != i) {
			p = p.next;
			pos = pos + 1;
		}
		return p;
	}

	// @ ensures \result >= 0;
	public /* @ pure @ */ int size() {
		return size;
	}

	public class Node {
		private E element;
		public Node next;

		public Node(E element) {
			this.element = element;
			this.next = null;
		}

		public E getElement() {
			return element;
		}
	}
}
