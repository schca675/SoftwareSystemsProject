package ss.week3.hotel;

/**
 * Guest with a name and possibly a room.
 * 
 * @author Cathy and Eric
 *
 */

public class Guest {
	private String name;
	private Room room; 

	/**
	 * Creates a <code>Guest</code> with the given name, without a room.
	 * 
	 * @param n
	 *            name of the new <code>Guest</code>
	 */

	/*@ pure */ public Guest(String n) {
		name = n;
	}

	/**
	 * Assigns a room to the <code>Guest</code>.
	 * 
	 * @param r
	 *            room assigned to the <code>Guest</code>
	 * @return if the checkin was successful
	 */
	public boolean checkin(Room r) {
		if (r.getGuest() != null) {
			return false;
		} else {
			room = r;
			r.setGuest(this);
			return true;
		}
	}

	/**
	 * Checks the <code>Guest</code> out.
	 * 
	 * @return if the checkout was successful
	 */
	public boolean checkout() {
		if (room == null) {
			return false;
		} else {
			room.setGuest(null);
			room = null;
			return true;
		}
	}

	/**
	 * returns the name of the <code>Guest</code>.
	 * 
	 * @return name of the guest
	 */
	/*@ pure */ public String getName() {
		return name;
	}

	/**
	 * returns the Room of the <code>Guest</code>.
	 * 
	 * @return Room of the guest or null if the guest has no room.
	 */
	/*@ pure */ public Room getRoom() {
		return room;
	}

	public String toString() {
		// return "This guest" + name + " with the room " + room.getNumber();
		return "This guest" + name;
	}

}
