package ss.week2.hotel;

public class Hotel {
	// Name of the hotel
	private String hotelName;
	private Room room1;
	private Room room2;
	private Password hotelPassword;
	
	//@ private invariant room1 != null && room2 != null;
	
	// Constructor of an hotel with a name and 2 empty rooms
	//@ ensures getFreeRoom() != null;
	//@ ensures getRoom1().getGuest() == null;
	//@ ensures getRoom2().getGuest() == null;
	//@ ensures getHotelName() == hotelName;
	public Hotel(String hotelName) {
		this.hotelName = hotelName;
		room1 = new Room(101);
		room2 = new Room(102);
		hotelPassword = new Password();
		assert room1.getGuest() == null && room2.getGuest() == null;
		assert this.hotelName == hotelName;
		assert getFreeRoom() != null;		
	}
	
	// Command to check in
	// First argument, password to check in
	// Second argument, name of the guest
	//@ ensures \result != null ==> getPassword().testWord(password);
	/*@ ensures \result != null ==> ((getRoom1().getGuest() != null) 
  	  @ 				==> (getRoom1().getGuest().getName() == guestName)) 
	  @ || ((getRoom2().getGuest() != null) ==> (getRoom2().getGuest().getName() == guestName)); */
	/*@ nullable*/ public Room checkIn(String password, String guestName) {	
		boolean freeRooms = getFreeRoom() != null;
		boolean rightPassword = getPassword().testWord(password);
		boolean guestNotIn = getRoom(guestName) == null;
		
		if (freeRooms && rightPassword && guestNotIn) {
			Room newRoom = getFreeRoom();
			Guest newGuest = new Guest(guestName);
			newGuest.checkin(newRoom);
			assert getPassword().testWord(password);
			assert newRoom.getGuest().getName().equals(guestName);
			return newRoom;
		} else {
			return null;
		}
	}
	
	// Command to check out
	// Good: Guest is checked out, safe deactivated 
	//@ ensures (getRoom1().getGuest() != null) ==> (getRoom1().getGuest().getName() != guestName);
	//@ ensures (getRoom2().getGuest() != null) ==> (getRoom2().getGuest().getName() != guestName);
	//@ ensures getRoom(guestName) == null;
	//@ ensures \old(getRoom(guestName)) != null ==> !\old(getRoom(guestName)).getSafe().isActive();
	public void checkOut(String guestName) {
		Room guestRoom = getRoom(guestName);
		if (guestRoom != null) {
			Guest leavingGuest = guestRoom.getGuest();
		    leavingGuest.checkout();
			guestRoom.getSafe().deactivate();
			assert guestRoom.getGuest() == null;
			assert !guestRoom.getSafe().isActive() && !guestRoom.getSafe().isOpen();
			assert getRoom(guestName) == null;
		}		
	}
	
	// Returns a free room, Null if no free room available.
	//@ ensures getRoom1().getGuest() != null && getRoom2().getGuest() != null ==> \result == null;
	//@ ensures getRoom1().getGuest() == null || getRoom2().getGuest() == null ==> \result != null;
	//@ ensures \result == null || \result.getGuest() == null;
	/*@ nullable*/ /*@ pure */ public Room getFreeRoom() {
		if (room1.getGuest() == null) {
			assert room1.getGuest() == null;
			return room1;
		} else {
			if (room2.getGuest() == null) {
				assert room2.getGuest() == null;
				return room2;
			} else {
				assert room1.getGuest() != null && room2.getGuest() != null;
				return null;
			}
		}
	}
	
	// Returns the room where the guest with the entered name is checked in.
	// Null if the guest does not have a room.
	/*@ ensures \result !=null <==> ((getRoom1().getGuest() != null) ==> 
	  @ 				(getRoom1().getGuest().getName().equals(guestName))) 
	  @ 				|| ((getRoom2().getGuest() != null) ==> 
	  @					(getRoom2().getGuest().getName().equals(guestName))); 
	 */
	//@ ensures \result == null || \result.getGuest().getName().equals(guestName);
	/*@ nullable*/ /*@ pure */ public Room getRoom(String guestName) {
		Room toReturn;
		if (room1.getGuest() != null && room1.getGuest().getName() == guestName) {
		    toReturn = room1;
		} else {
			if (room2.getGuest() != null && room2.getGuest().getName() == guestName) {
				toReturn = room2;
			} else {
				toReturn = null;
			}
		}
		assert toReturn == null || toReturn.getGuest().getName().equals(guestName);
		return toReturn;
	}
	
	// Returns password object of the hotel 
	//@ ensures \result == getPassword();
	/*@ pure */ public Password getPassword() {
		return hotelPassword;
	}
	
	// Returns a textual description of all rooms in the Hotel, 
	// including the name of the guest and the status of the safe in that room.
	/*@ pure */ public String toString() {
		String sentence = "The hotel " + getHotelName() + " has 2 rooms namely rooms : room " + 
							getRoom1().getNumber() + "whith guest: ";
		if (room1.getGuest() == null) {
			sentence = sentence + "none";
		} else {
			sentence = sentence + room1.getGuest().getName();
		}
		if (room1.getSafe().isActive()) {
			sentence = sentence + " safe: active;";
		} else {
			sentence = sentence + " safe: not active,";
		}
		
		sentence = sentence + " and room" + getRoom2().getNumber() + "whith guest: ";
		
		if (room2.getGuest() == null) {
			sentence = sentence + "none";
		} else {
			sentence = sentence + room2.getGuest().getName();
		}
		if (room2.getSafe().isActive()) {
			sentence = sentence + " safe: active.";
		} else {
			sentence = sentence + " safe: not active.";
		}				
		return sentence;
	}

	// Returns the room1.
	/*@ pure */ public Room getRoom1() {
		return room1;
	}
		
	// Returns the room2.
	/*@ pure */ public Room getRoom2() {
		return room2;
	}
	
	// Returns the hotel name;
	/*@ pure */ public String getHotelName() {
		return hotelName;
	}
	
}
