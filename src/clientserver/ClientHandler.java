package clientserver;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Arrays;

/**
 * ClientHandler.
 * 
 * @author Theo Ruys
 * @version 2005.02.21
 */
public class ClientHandler extends Thread {

	private Server server;
	private Socket sock;
	private BufferedReader in;
	private BufferedWriter out;
	private String clientName;
	private String[] features;
	private ArrayList<String> invited;
	private ArrayList<String> invites;
	private int playerNumber;
	private String opponentName;
	private boolean loop;

	/**
	 * Constructs a ClientHandler object Initialises both Data streams. @
	 * requires server != null && sock != null;
	 */
	public ClientHandler(Server serverArg, Socket sockArg) throws IOException {
		this.server = serverArg;
		this.sock = sockArg;
		this.in = new BufferedReader(new InputStreamReader(
				sock.getInputStream()));
		this.out = new BufferedWriter(new OutputStreamWriter(
				sock.getOutputStream()));
		this.loop = true;
		this.invited = new ArrayList<String>();
		this.invites = new ArrayList<String>();
		this.playerNumber = -1;
	}

	/**
	 * This method takes care of sending messages from the Client. Every message
	 * that is received, is preprended with the name of the Client, and the new
	 * message is offered to the Server for broadcasting. If an IOException is
	 * thrown while reading the message, the method concludes that the socket
	 * connection is broken and shutdown() will be called.
	 */
	public void run() {
		while (loop) {
			try {
				String line = in.readLine();
				String[] command = line.split("\\s+");
				switch (command[0]) {
				case Client.CONNECT:
					if (command.length >= 2) {
						if (!server.nameExists(command[1])) {
							clientName = command[1];
							if (command.length > 2) {
								features = Arrays.copyOfRange(command, 2,
										command.length - 1);
							}
							sendMessage(Server.ACCEPT_CONNECT
									+ " Feature array gescheiden met spaties");
							server.broadcastLobby();
							server.print(": " + getClientName() + " has joined");
						} else {
							sendMessage(Server.ERROR + " Name in use");
						}
					} else {
						sendMessage(Server.ERROR + " Invalid arguments");
					}
					//TODO: voeg client toe aan server (lobby)
					//TODO: broadcast de nieuwe lobby aan iedereen zonder game
					break;
				case Client.QUIT:
					//TODO: invites van deze client weghalen?
					//TODO: broadcast de lobby als de client geen game had aan iedereen zonder game inclusief=
					shutdown();
					break;
				case Client.INVITE:
					if (command.length >= 2) {
						if (server.nameExists(command[1])) {
							if (!invited.contains(command[1])) {
								server.sendMessage(command[1], Server.INVITE
										+ " " + getClientName());
							} else {
								sendMessage(Server.ERROR
										+ " Already invited this client");
							}
						} else {
							sendMessage(Server.ERROR + " Name doesn't exist");
						}
					} else {
						sendMessage(Server.ERROR + " Invalid arguments");
					}
					break;
				case Client.ACCEPT_INVITE:
					if (command.length == 2) {
						if (invites.contains(command[1])) {
							invites.remove(command[1]);
							//TODO: extras verzenden (spectators?)
							sendMessage(Server.GAME_START + " "
									+ getClientName() + " " + command[1]);
							server.sendMessage(command[1], Server.GAME_START
									+ " " + getClientName() + " " + command[1]);
							sendMessage(Server.REQUEST_MOVE);
						} else {
							sendMessage(Server.ERROR
									+ " Not invited by this client");
						}
					} else {
						sendMessage(Server.ERROR + " Invalid arguments");
					}
					break;
				case Client.DECLINE_INVITE:
					if (command.length == 2) {
						if (invites.contains(command[1])) {
							invites.remove(command[1]);
							server.sendMessage(command[1], Server.ERROR
									+ " Invite declined");
						} else {
							sendMessage(Server.ERROR
									+ " Not invited by this client");
						}
					} else {
						sendMessage(Server.ERROR + " Invalid arguments");
					}
					break;
				case Client.MOVE:
					if (command.length == 2) {
						//TODO: zelf bord bijhouden voor nummer en move ok checken
						sendMessage(Server.MOVE_OK + " " + playerNumber + " "
								+ command[1]);
						server.sendMessage(opponentName, Server.MOVE_OK + " "
								+ playerNumber + " " + command[1]);
						server.sendMessage(opponentName, Server.REQUEST_MOVE);
						//TODO: gewonnen is game end sturen
					} else {
						sendMessage(Server.REQUEST_MOVE);
					}
					break;
				case Client.CHAT:
					if (command.length >= 2) {
						server.broadcast(line);
					} else {
						sendMessage(Server.ERROR + " Invalid arguments");
					}
					break;
				case Client.REQUEST_BOARD:
					//TODO: zelf bord bijhouden om op te sturen
					break;
				case Client.REQUEST_LOBBY:
					sendMessage(Server.LOBBY + server.getLobby());
					break;
				case Client.REQUEST_LEADERBOARD:
					//TODO: leaderbords opslaan
					break;
				default:
					sendMessage(Server.ERROR + " Invalid command");
				}
			} catch (IOException | NullPointerException e) {
				shutdown();
			}
		}
	}

	/**
	 * This method can be used to send a message over the socket connection to
	 * the Client. If the writing of a message fails, the method concludes that
	 * the socket connection has been lost and shutdown() is called.
	 */
	public void sendMessage(String msg) {
		try {
			String[] command = msg.split("\\s+");
			switch (command[0]) {
			case Server.INVITE:
				invites.add(command[1]);
				break;
			case Server.GAME_START:
				if (clientName.equals(command[1])) {
					playerNumber = 0;
					opponentName = command[2];
				} else {
					playerNumber = 1;
					opponentName = command[1];
				}
				server.broadcastLobby();
				//TODO: voeg bord toe
				break;
			case Server.GAME_END:
				//TODO: bord afsluiten en enden
				playerNumber = -1;
				break;
			case Server.MOVE_OK:
				//TODO: move doen bijbehorende speler
			}
			out.write(msg);
			out.newLine();
			out.flush();
			server.print(" to " + getClientName() + ": " + msg);
		} catch (IOException e) {
			shutdown();
		}
	}

	/**
	 * returns the name of the client
	 * 
	 * @return the name of the client
	 */
	public String getClientName() {
		return clientName;
	}

	/**
	 * returns the features of the client
	 * 
	 * @return the features of the client
	 */
	public String[] getClientFeatures() {
		return features;
	}

	/**
	 * returns wheter the client is playing a game
	 */
	public boolean inGame() {
		//TODO: verbeteren
		return playerNumber != -1;
	}

	/**
	 * This ClientHandler signs off from the Server and subsequently sends a
	 * last broadcast to the Server to inform that the Client is no longer
	 * participating in the chat.
	 */
	private void shutdown() {
		if (!inGame()) {
			server.broadcastLobby();
		}
		server.print(": " + getClientName() + " has left");
		server.removeHandler(this);
		loop = false;
	}

} // end of class ClientHandler
