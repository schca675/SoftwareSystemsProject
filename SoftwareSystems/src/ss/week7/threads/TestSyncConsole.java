package ss.week7.threads;

import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

public class TestSyncConsole extends Thread {
	@Override
	public void run() {
		sum();
	}
	
	private void sum() {
//		synchronized (System.in) {
//			int a = SyncConsole.readInt(this.getName() + ": " + "First number");
//			int b = SyncConsole.readInt(this.getName() + ": " + "Second number");
//			int sum = a + b;
//			SyncConsole.println(this.getName() + ": " + a + " + " + b + " = " + sum);
//		}
		Lock myLock = new ReentrantLock();
		myLock.lock();
		try {
			int a = SyncConsole.readInt(this.getName() + ": " + "First number");
			int b = SyncConsole.readInt(this.getName() + ": " + "Second number");
			int sum = a + b;
			SyncConsole.println(this.getName() + ": " + a + " + " + b + " = " + sum);
		}  finally {
			myLock.unlock();
		}
	}
	
	public static void main(String[] args) {
		TestSyncConsole a = new TestSyncConsole();
		TestSyncConsole b = new TestSyncConsole();
		a.start();
		b.start();
	}
}
