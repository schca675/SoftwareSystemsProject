package ss.week3;

public class TimedPassword extends Password {
	public static final double DEFAULTEXPIRATION = 10e5;
	private double validTime;
	private double creationTime;
	
	public TimedPassword() {
		this(DEFAULTEXPIRATION);			
	}
	
	public TimedPassword(double expirationTime) {
		super();
		validTime = expirationTime;
		creationTime = java.lang.System.currentTimeMillis();
	}
	
	public Boolean isExpired() {
		double currentTime = java.lang.System.currentTimeMillis();
		return currentTime - creationTime > validTime;		
	}
	
	public boolean setWord(String oldpass, String newpass) {
		if (super.setWord(oldpass, newpass)) {
			creationTime = java.lang.System.currentTimeMillis();
			return true;
		} else {
			return false;
		}
	}
}
