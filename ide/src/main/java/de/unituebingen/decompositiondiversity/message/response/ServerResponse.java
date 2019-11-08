package de.unituebingen.decompositiondiversity.message.response;

public class ServerResponse<T> {
	private String status;
	private T data;
	
	public ServerResponse(){
		
	}
	
	public ServerResponse(String status, T data){
		this.status = status;
		this.data = data;
	}
 
	public String getStatus() {
		return status;
	}
 
	public void setStatus(String status) {
		this.status = status;
	}
 
	public Object getData() {
		return data;
	}
 
	public void setData(T data) {
		this.data = data;
	}
}
