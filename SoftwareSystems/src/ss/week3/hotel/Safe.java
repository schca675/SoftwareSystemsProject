package ss.week3.hotel;

public class Safe {
	// Password to activate and open the safe.
	private Password passwordSafe;
	private boolean activated;
	private boolean open;

	// Constructor which builds a new safe with its password.
	//@ ensures getPassword() != null;
	//@ ensures !isActive();
	//@ ensures !isOpen();
	public Safe() {
	    passwordSafe = new Password();
	    open = false;
	    activated = false;
	}
	
	// Activates the safe if entered password is the correct one;
	// We chose: If entered password is wrong, the safe gets deactivated.
	//@ ensures getPassword().testWord(password) ==> isActive();
	public void activate(String password) {
		activated = getPassword().testWord(password);
	}

	// Closes the safe and deactivates it.
	//@ ensures !isActive();
	//@ ensures !isOpen();
	public void deactivate() {
		activated = false;
		open = false;		
	}

	// Opens the safe if it is active and if the password is correct.
	// We chose: if the entered password is wrong, the safe closes 
	// and if it is deactivated nothing happens.
	//@ ensures getPassword().testWord(password) && isActive() ==> isOpen();
	public void open(String password) {
		if (isActive()) {
		    open = getPassword().testWord(password);
		}
	}

	// Closes the safe (but does not change its activity status).
	//@ ensures !isOpen();
	//@ ensures isActive() == \old (isActive());
	public void close() {
		open = false;
	}

	// Indicates whether the safe is active or not.
	/*@pure */ public boolean isActive() {
		return activated;
	}

	// Indicates whether the safe is open or not.
	/*@pure */ public boolean isOpen() {
		return open;
	}

	// Returns the password object on which the method testWord can be called to
	// check the password.
	/*@pure */ public Password getPassword() {
		return passwordSafe;
	}
	
}
