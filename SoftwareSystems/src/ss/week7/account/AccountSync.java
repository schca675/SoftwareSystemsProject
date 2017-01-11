package ss.week7.account;

public class AccountSync {
	public static void main(String[] args) {
		Account account = new Account();
		int freq = 100000;
		Thread adding = new Thread(new MyThread(50.00, freq, account));
		Thread removing = new Thread(new MyThread(-50.00, freq, account));
		adding.start();
		removing.start();		
		try {
			removing.join();
			adding.join();
		} catch (InterruptedException e) {
			System.err.println(e);
		}
		System.out.println(account.getBalance());
	}
}
