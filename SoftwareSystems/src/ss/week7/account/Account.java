package ss.week7.account;

public class Account {
	protected double balance = 0.0;

	public synchronized void transaction(double amount) {
		while (balance + amount < -1000) {
			try {
				wait();
			} catch (InterruptedException e) {
				System.err.println(e);
			}
		}
		balance = balance + amount;
		notifyAll();
	}
	
	public synchronized double getBalance() {
		return balance;

	}
}
