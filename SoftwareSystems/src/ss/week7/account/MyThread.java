package ss.week7.account;

public class MyThread implements Runnable {
	private double theAmount;
	private int theFrequency;
	private Account theAccount;

	//@ requires frequency >= 1;
	public MyThread(double amount, int frequency, Account account) {
		this.theAmount = amount;
		this.theFrequency = frequency;
		this.theAccount = account;
	}
	
	@Override
	public void run() {
		for (int i = 1; i <= theFrequency; i++) {
			theAccount.transaction(theAmount);
		}
	}
}
