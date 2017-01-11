package ss.week7.threads;

public class SynchronizedIntCell implements IntCell {
	private int value = 0;
	private boolean read = true;

	@Override
	public synchronized void setValue(int val) {
		while (!read) {
			try {
				wait();
			} catch (InterruptedException e) {
				System.err.println(e);
			}
		}
		synchronized (System.out) {
			read = false;
			this.value = val;
			notifyAll();
		}
	}

	@Override
	public synchronized int getValue() {
		while (read) {
			try {
				wait();
			} catch (InterruptedException e) {
				System.err.println(e);
			}
		}
		synchronized (System.out) {
			read = true;
			notifyAll();
			return value;
		}
	}

}
