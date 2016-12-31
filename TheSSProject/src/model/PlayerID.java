package model;


public enum PlayerID {
	
	
	/* Note to us: 
	 * If we want to have more distinct players, we could change this.
	 * 
	 */
	
	
	// Since the game only needs two players, there exist two playerID's.
	X, O;
	
	/**
	 * Returns the other player ID.
	 * 
	 * @return the other possible player ID.
	 */
	/*@
	 @ ensures this == PlayerID.X ==> \result == PlayerID.O;
	 @ ensures this == PlayerID.O ==> \result == PlayerID.X;
	 */
	public PlayerID other() {
		if (this == X) {
			return O;
		} else {
			return X;
		}
	}
	
	/**
	 * Returns the String object of this object.
	 */
	//@ ensures \result == "X" || \result == "O";
	@Override
	public String toString() {
		switch (this) {
			case X:
				return "X";
			default:
				return "O";
		}
	}

}
