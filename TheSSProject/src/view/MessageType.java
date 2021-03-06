package view;

public enum MessageType {
	INVALID_ADDRESS, 
	INVALID_PORT,	
	PROBLEM_DISCONNECTING, 
	INVALID_COORDINATES, 
	SOCKET_FAILURE,
	INVALID_INPUT, 
	INVALID_STRATEGY, 
	STREAM_FAILURE, 
	WRITING_FAILURE, 
	RETURN_START, 
	SERVER_LISTENING, 
	PROTOCOL_IRREGULARITIES, 
	SERVER_ILLEGAL_MOVE, 
	
	SOCKET_CREATED, 
	GOT_SERVER_CAP,
	SENT_CLIENT_CAP,
	GOT_ID,
	GAME_START,
	YOUR_TURN,
	MOVE_MADE;
}
