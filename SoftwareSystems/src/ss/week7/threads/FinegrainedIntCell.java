package ss.week7.threads;

import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class FinegrainedIntCell implements IntCell {
	private int value = 0;
	private final Lock myLock = new ReentrantLock();
	private final Condition notRead = myLock.newCondition();
	private final Condition notWritten = myLock.newCondition();
	private boolean read = true;
	
	@Override
	public void setValue(int val) {
		myLock.lock();
		try {
			while (!read) {
				notWritten.await();
			}
			this.value = val;
			read = false;
			notRead.signal();
		} catch (InterruptedException e) {
			System.err.println(e);
		} finally {
			myLock.unlock();
		}
	}

	@Override
	public int getValue() {
		int result = 0;
		myLock.lock();
		try {
			while (read) {
				notRead.await();
			}
			notWritten.signal();
			read = true;
			result = value;
		} catch (InterruptedException e) {
			System.err.println(e);
		} finally {	
			myLock.unlock();
		}
		return result;
	}

}
